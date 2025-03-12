#include <tsl/ordered_map.h>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <functional>
#include <vector>
#include <string>
#include <memory>
#include <unordered_map>
#include <iostream>
#include <unordered_set>

#include <Windows.h>

#include <clang-c/Index.h>
#include <nlohmann/json.hpp>

#define ALIGN_UP(value, alignment) (((value) + (alignment) - 1) & ~((alignment) - 1))

enum json_category {
    ENUM_TYPE = 0,
    STRUCT_TYPE = 1,
    UNION_TYPE = 2,
    TYPEDEF_TYPE = 3,
    FUNCTION_TYPE = 4
};

struct CXTypeHash {
    std::size_t operator()(const CXType &t) const noexcept {
        const std::size_t hash1 = std::hash<int>{}(t.kind);
        const std::size_t hash2 = std::hash<void *>{}(t.data[0]);
        const std::size_t hash3 = std::hash<void *>{}(t.data[1]);

        return hash1 ^ hash2 << 1 ^ hash3 << 2;
    }
};

struct CXTypeEqual {
    bool operator()(const CXType &lhs, const CXType &rhs) const {
        return clang_equalTypes(lhs, rhs);
    }
};

uint32_t anonymous_type_counter = 0;
std::unordered_map<CXType, std::string, CXTypeHash, CXTypeEqual> anonymous_type_map;
tsl::ordered_map<CXType, std::pair<nlohmann::json, json_category>, CXTypeHash, CXTypeEqual>
declared_types;

bool type_declared(const CXType &field_type) {
    return declared_types.contains(field_type);
}

void insert_type_declared(const CXType &field_type, const nlohmann::json &json, json_category cat) {
    declared_types[field_type] = {json, cat};
}

void float_type_declared(const CXType &field_type) {
    const auto value = declared_types[field_type];
    declared_types.erase(field_type);

    declared_types[field_type] = value;
}

void remove_type_declaration(const CXType &field_type) {
    declared_types.erase(field_type);
}

void create_anon_type_name(const CXType &str) {
    const CXCursor decl_cursor = clang_getTypeDeclaration(str);
    assert(clang_Cursor_isAnonymous(decl_cursor), "type is not anonymous");

    if (anonymous_type_map.contains(str))
        return;

    const char *prefix_name;
    switch (clang_getCursorKind(decl_cursor)) {
    case CXCursor_StructDecl:
        prefix_name = "struct";
        break;
    case CXCursor_ClassDecl:
        prefix_name = "class";
        break;
    case CXCursor_UnionDecl:
        prefix_name = "union";
        break;
    case CXCursor_EnumDecl:
        prefix_name = "enum";
        break;
    }

    const auto anon_type_name = std::format("__anon_{}{}", prefix_name, ++anonymous_type_counter);
    anonymous_type_map[str] = anon_type_name;
}

const char *try_get_anon_name(const CXType &str) {
    if (anonymous_type_map.contains(str)) {
        return anonymous_type_map[str].c_str();
    }

    return nullptr;
};

nlohmann::json &get_type_json(const CXType &type) {
    return std::get<0>(declared_types[type]);
}

// removed the prefix "struct", "union", "enum", and "class"
// also gives anonymous name to field types
std::string normalize_type_name(const CXType &type, const uint32_t pointer_level = 0) {
    auto current_type = clang_getUnqualifiedType(type);
    if (current_type.kind == CXType_ConstantArray ||
        current_type.kind == CXType_IncompleteArray ||
        current_type.kind == CXType_VariableArray) {
        current_type = clang_getElementType(current_type);
    } else if (current_type.kind == CXType_Elaborated) {
        current_type = clang_Type_getNamedType(current_type);
    }

    if (current_type.kind == CXType_Pointer) {
        const CXType next_type = clang_getPointeeType(current_type);
        if (next_type.kind != CXType_Invalid) {
            return normalize_type_name(next_type, pointer_level + 1);
        }
    }

    const CXCursor decl_cursor = clang_getTypeDeclaration(current_type);
    if (!clang_Cursor_isNull(decl_cursor)) {
        const CXCursorKind kind = clang_getCursorKind(decl_cursor);
        if (kind == CXCursor_StructDecl ||
            kind == CXCursor_ClassDecl ||
            kind == CXCursor_UnionDecl ||
            kind == CXCursor_EnumDecl) {
            if (clang_Cursor_isAnonymous(decl_cursor)) {
                create_anon_type_name(current_type);
            }
        }
    }

RETURN_SPELLING:
    const auto out_spelling = try_get_anon_name(current_type);
    if (!out_spelling) {
        const auto spelling = clang_getTypeSpelling(current_type);
        std::string result = std::string(clang_getCString(spelling)) +
                             std::string(
                                 pointer_level, '*');

        clang_disposeString(spelling);
        return result;
    }

    return std::string(out_spelling) + std::string(pointer_level, '*');
};

CXChildVisitResult visit_cursor(CXCursor cursor, CXCursor parent, CXClientData) {
    auto handle_container_decl = [](const CXCursor &target_cursor, const json_category cat) {
        nlohmann::json struct_decl;

        bool is_forward_declared = clang_equalCursors(clang_getCursorDefinition(target_cursor),
                                                      clang_getNullCursor());

        const CXType structure_type = clang_getCursorType(target_cursor);
        if (type_declared(structure_type)) {
            // check if previously declared structure is empty
            nlohmann::json &previous_decl = get_type_json(structure_type);
            if (previous_decl["size"] != 0 && !struct_decl["members"].empty()) {
                // skip redefinition
                return;
            }

            struct_decl = previous_decl;
        }

        std::string type_name;
        const auto spelling = clang_getTypeSpelling(structure_type);
        if (clang_Cursor_isAnonymousRecordDecl(target_cursor) ||
            clang_Cursor_isAnonymous(target_cursor)) {
            // is anonynmous
            type_name = normalize_type_name(structure_type);

            const auto parent_cursor = clang_getCursorSemanticParent(target_cursor);
            if (!clang_Cursor_isNull(parent_cursor) && clang_Cursor_isAnonymous(target_cursor)) {
                const CXType parent_type = clang_getCursorType(parent_cursor);

                nlohmann::json &parent_structure = get_type_json(parent_type);
                auto &members = parent_structure["members"];

                nlohmann::json member_info = {};
                member_info["name"] = type_name;

                long long expected_offset = 0;
                if (!parent_structure.contains("isUnion") || !parent_structure["isUnion"]) {
                    if (!members.empty()) {
                        auto &back = members.back();

                        const auto bit_size = back["bitSize"].get<long long>();
                        const auto prev_offset = back["offset"].get<long long>();

                        const auto prev_end_offset = prev_offset + (bit_size + 7) / 8;
                        const auto union_align = clang_Type_getAlignOf(structure_type);
                        if (prev_end_offset % union_align == 0)
                            expected_offset = prev_end_offset;
                        else
                            expected_offset = ALIGN_UP(prev_end_offset, union_align);
                    }
                }

                member_info["bitSize"] = clang_Type_getSizeOf(structure_type) * 8;
                member_info["offset"] = expected_offset;
                member_info["type"] = type_name;

                members.push_back(member_info);
            }

        } else {
            type_name = std::string(clang_getCString(spelling));
        }

        struct_decl["name"] = type_name;
        struct_decl["members"] = nlohmann::json::array();

        if (cat == UNION_TYPE)
            struct_decl["isUnion"] = true;

        if (cat == ENUM_TYPE) {
            // set enum size
            const auto underlying_type = clang_getEnumDeclIntegerType(target_cursor);
            struct_decl["size"] = is_forward_declared ? 0 : clang_Type_getSizeOf(underlying_type);
            struct_decl["isFlags"] = true;
        } else {
            // set default size
            struct_decl["size"] = is_forward_declared ? 0 : clang_Type_getSizeOf(structure_type);
        }

        // insert classes as structures
        insert_type_declared(structure_type, struct_decl, cat);

        // we do not want to visit classes
        clang_visitChildren(target_cursor, visit_cursor, nullptr);
        float_type_declared(structure_type);

        clang_disposeString(spelling);
    };

    switch (clang_getCursorKind(cursor)) {
    case CXCursor_StructDecl:
        handle_container_decl(cursor, STRUCT_TYPE);
        return CXChildVisit_Continue;
    case CXCursor_UnionDecl:
        handle_container_decl(cursor, UNION_TYPE);
        return CXChildVisit_Continue;
    case CXCursor_EnumDecl:
        handle_container_decl(cursor, ENUM_TYPE);
        return CXChildVisit_Continue;
    case CXCursor_FunctionDecl:
        handle_container_decl(cursor, FUNCTION_TYPE);
        return CXChildVisit_Continue;
    case CXCursor_ClassDecl:
        handle_container_decl(cursor, STRUCT_TYPE);
        return CXChildVisit_Continue;

    case CXCursor_EnumConstantDecl: {
        const CXCursorKind parent_kind = clang_getCursorKind(parent);
        assert(parent_kind == CXCursor_EnumDecl,
               "parent is not enum declaration");

        const CXType parent_type = clang_getCursorType(parent);
        nlohmann::json &parent_enum = get_type_json(parent_type);
        nlohmann::json &members = parent_enum["members"];

        const CXString name = clang_getCursorSpelling(cursor);
        nlohmann::json member_info = {};
        member_info["name"] = clang_getCString(name);
        member_info["value"] = clang_getEnumConstantDeclValue(cursor);

        members.push_back(member_info);
        clang_disposeString(name);
        break;
    }

    // relevant structure items
    case CXCursor_FieldDecl: {
        const CXCursorKind parent_kind = clang_getCursorKind(parent);
        assert(
            parent_kind == CXCursor_StructDecl ||
            parent_kind == CXCursor_ClassDecl ||
            parent_kind == CXCursor_UnionDecl,
            "parent is not struct/class declaration");

        const CXType parent_type = clang_getCursorType(parent);
        if (!type_declared(parent_type))
            clang_visitChildren(cursor, visit_cursor, nullptr);

        nlohmann::json &parent_structure = get_type_json(parent_type);
        auto &members = parent_structure["members"];

        nlohmann::json member_info = {};

        const CXString name = clang_getCursorSpelling(cursor);
        member_info["name"] = clang_getCString(name);

        const auto bit_offset = clang_Cursor_getOffsetOfField(cursor);
        member_info["offset"] = bit_offset / 8;

        const CXType field_type = clang_getCursorType(cursor);

        long long element_count = 1;
        if (field_type.kind == CXType_ConstantArray) {
            auto current_array_type = field_type;
            while (current_array_type.kind == CXType_ConstantArray) {
                long long size = clang_getArraySize(current_array_type);
                assert(size >= 0, "array size must be positive");

                element_count *= size;
                current_array_type = clang_getArrayElementType(current_array_type);
            }

            member_info["type"] = normalize_type_name(clang_getArrayElementType(field_type));
            member_info["arrsize"] = element_count;
        } else {
            bool is_fun_pointer = false;
            if (field_type.kind == CXType_Pointer) {
                // check if function proto
                auto curr_type = field_type;
                while (curr_type.kind == CXType_Pointer)
                    curr_type = clang_getPointeeType(curr_type);

                if (curr_type.kind == CXType_FunctionProto ||
                    curr_type.kind == CXType_FunctionNoProto) {
                    is_fun_pointer = true;
                }
            }

            if (is_fun_pointer)
                member_info["type"] = "void*";
            else
                member_info["type"] = normalize_type_name(field_type);
        }

        if (clang_Cursor_isBitField(cursor)) {
            member_info["bitOffset"] = bit_offset % 8;
            member_info["bitSize"] = clang_getFieldDeclBitWidth(cursor);
            member_info["bitfield"] = true;
        } else {
            member_info["bitSize"] = clang_Type_getSizeOf(field_type) * 8;
        }

        // todo correct way to do this would be checking the attributes
        // make sure its not a __ptr32
        if (member_info["type"] == "void*") {
            auto ptr_bit_size = member_info["bitSize"].get<long long>() / element_count;
            if (ptr_bit_size == 32) {
                member_info["type"] = "unsigned int";
            }
        }

        // todo clean up so not checking json fields and actual values instead
        // check if back element is of same type and same offset
        if (!members.empty()) {
            auto &back = members.back();

            bool similar_field = back["type"] == member_info["type"] &&
                                 back["offset"] == member_info["offset"];
            if (similar_field) {
                if (back.contains("bitOffset") == member_info.contains("bitOffset")) {
                    if (!back.contains("bitOffset") ||
                        back["bitOffset"] == member_info["bitOffset"]) {
                        back["name"] = member_info["name"];
                        clang_disposeString(name);
                        break;
                    }
                }
            }
        }

        members.push_back(member_info);
        clang_disposeString(name);
        break;
    }
    case CXCursor_TypedefDecl: {
        const CXType underlying_type = clang_getTypedefDeclUnderlyingType(cursor);
        if (type_declared(clang_getCursorType(cursor)))
            break;

        bool is_fun_pointer = false;

        const CXString typedef_name = clang_getCursorSpelling(cursor);
        if (underlying_type.kind == CXType_Pointer) {
            // check if function proto
            auto curr_type = underlying_type;
            while (curr_type.kind == CXType_Pointer)
                curr_type = clang_getPointeeType(curr_type);

            if (curr_type.kind == CXType_FunctionProto ||
                curr_type.kind == CXType_FunctionNoProto) {
                is_fun_pointer = true;
            }
        }

        if (underlying_type.kind == CXType_FunctionProto ||
            underlying_type.kind == CXType_FunctionNoProto) {
            // function type
            nlohmann::json function_info;
            function_info["args"] = {};

            auto arg_count = clang_getNumArgTypes(underlying_type);
            for (auto i = 0; i < arg_count; i++) {
                auto arg = clang_getArgType(underlying_type, i);
                auto name = clang_getCursorSpelling(clang_getTypeDeclaration(arg));

                nlohmann::json arg_info;
                //arg_info["name"] = clang_getCString(name);
                arg_info["name"] = "";
                arg_info["type"] = normalize_type_name(arg);

                clang_disposeString(name);

                function_info["args"].push_back(arg_info);
            }

            const CXType return_type = clang_getResultType(underlying_type);
            function_info["rettype"] = normalize_type_name(return_type);
            function_info["name"] = clang_getCString(typedef_name);

            // callconv
            switch (clang_getFunctionTypeCallingConv(underlying_type)) {
            case CXCallingConv_C:
                function_info["callconv"] = "cdecl";
                break;
            case CXCallingConv_X86StdCall:
                function_info["callconv"] = "stdcall";
                break;
            case CXCallingConv_X86FastCall:
            case CXCallingConv_X86ThisCall:
            case CXCallingConv_X86RegCall:
            case CXCallingConv_X86_64Win64:
            case CXCallingConv_X86_64SysV:
            case CXCallingConv_X86VectorCall:
            default:
                function_info["callconv"] = "fastcall";
                break;
            }

            // noreturn
            // this is definitely no true but we can ignore this for now
            // function_info["noreturn"] = false;

            insert_type_declared(clang_getCursorType(cursor), function_info, FUNCTION_TYPE);
        } else {
            // other
            auto name = clang_getCString(typedef_name);
            auto type = normalize_type_name(underlying_type);

            const std::initializer_list<std::string> ignored_types = {
                "__C_ASSERT__", "type", "_Type", "nullptr_t"};
            if (std::ranges::find(ignored_types, std::string(name)) == ignored_types.end() && name
                != type) {
                nlohmann::json type_info;
                type_info["name"] = name;

                if (is_fun_pointer)
                    type_info["type"] = "void*";
                else
                    type_info["type"] = type;

                static std::unordered_map<std::string, std::string> defined_types = {};
                if (defined_types.contains(type_info["name"])) {
                    // repeating typedef, not going to insert
                    // auto &prev_type = defined_types[type_info["name"]];
                    // auto curr_type = type_info["type"].get<std::string>();
                    // assert(prev_type == curr_type, "repeating typedef with different type");
                } else {
                    insert_type_declared(clang_getCursorType(cursor), type_info, TYPEDEF_TYPE);
                    defined_types[type_info["name"]] = type_info["type"];
                }
            }
        }

        clang_disposeString(typedef_name);
        break;
    }
    }

    return CXChildVisit_Recurse;
}

int generateHeader(const char *target_arg, const char *output_header, const char *stub_source) {
    // setup arguments
    std::vector<std::string> clang_args =
    {
        // "-I" + std::string(argv[1]),
        "-x",
        "c++",
        "-fms-extensions",
        "-Xclang",
        "-ast-dump",
        "-fsyntax-only",
        "-fms-extensions",
        target_arg
    };

    std::vector<const char *> c_args;
    for (const auto &arg : clang_args)
        c_args.push_back(arg.c_str());

    if (const auto index = clang_createIndex(0, 1)) {
        CXTranslationUnit tu = nullptr;
        const auto error = clang_parseTranslationUnit2(
            index,
            stub_source,
            c_args.data(),
            static_cast<int>(c_args.size()),
            nullptr,
            0,
            CXTranslationUnit_DetailedPreprocessingRecord |
            CXTranslationUnit_PrecompiledPreamble |
            CXTranslationUnit_SkipFunctionBodies |
            CXTranslationUnit_ForSerialization,
            &tu);

        if (error == CXError_Success) {
            const CXCursor cursor = clang_getTranslationUnitCursor(tu);
            clang_visitChildren(cursor, visit_cursor, nullptr);
        } else {
            printf("CXError: %d\n", error);
            return EXIT_FAILURE;
        }

        clang_disposeTranslationUnit(tu);
    }

    nlohmann::json root_type_object;
    root_type_object["enums"] = {};
    root_type_object["structUnions"] = {};
    root_type_object["types"] = {};
    root_type_object["functions"] = {};

    for (auto &val : declared_types | std::views::values) {
        auto &[body, type] = val;
        switch (type) {
        case ENUM_TYPE:
            root_type_object["enums"].push_back(body);
            break;
        case STRUCT_TYPE:
        case UNION_TYPE:
            root_type_object["structUnions"].push_back(body);
            break;
        case TYPEDEF_TYPE:
            root_type_object["types"].push_back(body);
            break;
        case FUNCTION_TYPE:
            root_type_object["functions"].push_back(body);
            break;
        }
    }

    std::ofstream out(output_header, std::ios::trunc);
    out << root_type_object.dump(4) << std::endl;

    anonymous_type_counter = 0;
    anonymous_type_map = {};
    declared_types = {};

    return EXIT_SUCCESS;
}

int main(const int argc, char **argv) {
    // setup stub file
    const std::filesystem::path current_path = std::filesystem::current_path();
    const auto stub_source = current_path / "stub_include.cpp";

    const std::vector<std::string> target_headers = {
        "phnt.h"
    };

    std::ofstream include_stub(stub_source, std::ios::out | std::ios::trunc);
    for (auto &include : target_headers)
        include_stub << std::format("#include <{}>\n", include);

    include_stub.close();

    generateHeader("-target x86_64-windows-msvc", "x86_64-windows.json",
                   stub_source.string().c_str());
    generateHeader("-target x86-windows-msvc", "x86-windows.json", stub_source.string().c_str());

    return EXIT_SUCCESS;
}