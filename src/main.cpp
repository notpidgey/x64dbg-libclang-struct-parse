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

enum json_category {
    ENUM_TYPE = 0,
    STRUCT_TYPE = 1,
    UNION_TYPE = 2,
    TYPEDEF_TYPE = 3,
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

tsl::ordered_map<CXType, std::pair<nlohmann::json, json_category>, CXTypeHash, CXTypeEqual> declared_types;

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

void remove_type_declaration(const CXType& field_type) {
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

    const auto anon_type_name = std::format("__anonymous_{}{}", prefix_name, ++anonymous_type_counter);
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
std::string normalize_field_type_name(const CXType &type, const uint32_t pointer_level = 0) {
    auto current_type = type;
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
            return normalize_field_type_name(next_type, pointer_level + 1);
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
        std::string result = std::string(clang_getCString(spelling)) + std::string(pointer_level, '*');

        clang_disposeString(spelling);
        return result;
    }

    return std::string(out_spelling) + std::string(pointer_level, '*');
};

CXChildVisitResult visit_cursor(CXCursor cursor, CXCursor parent, CXClientData _2) {
    auto handle_container_decl = [](const CXCursor &target_cursor, const json_category cat) {
        nlohmann::json struct_decl;

        const CXType structure_type = clang_getCursorType(target_cursor);
        if (clang_equalCursors(clang_getCursorDefinition(target_cursor), clang_getNullCursor()) ||
            type_declared(structure_type))
            return;

        std::string type_name;
        const auto spelling = clang_getTypeSpelling(structure_type);
        if (clang_Cursor_isAnonymousRecordDecl(target_cursor) || clang_Cursor_isAnonymous(target_cursor)) {
            if (!try_get_anon_name(structure_type))
                create_anon_type_name(structure_type);

            type_name = try_get_anon_name(structure_type);
        } else {
            type_name = std::string(clang_getCString(spelling));
        }

        struct_decl["name"] = type_name;
        struct_decl["members"] = {};

        // if (type_name == "_RTL_BALANCED_NODE")
        //     __debugbreak();

        if (cat == UNION_TYPE)
            struct_decl["isUnion"] = true;

        if (cat == ENUM_TYPE) {
            const auto underlying_type = clang_getEnumDeclIntegerType(target_cursor);
            auto size = clang_Type_getSizeOf(underlying_type) * 8;

            struct_decl["size"] = size;
            struct_decl["isBitField"] = true;
        }

        insert_type_declared(structure_type, struct_decl, cat);
        clang_visitChildren(target_cursor, visit_cursor, nullptr);

        if (!get_type_json(structure_type)["members"].empty())
            float_type_declared(structure_type);
        else
            remove_type_declaration(structure_type);

        clang_disposeString(spelling);
    };

    switch (const auto cursor_kind = clang_getCursorKind(cursor)) {
        case CXCursor_StructDecl:
            handle_container_decl(cursor, STRUCT_TYPE);
            return CXChildVisit_Continue;
        case CXCursor_UnionDecl:
            handle_container_decl(cursor, UNION_TYPE);
            return CXChildVisit_Continue;
        case CXCursor_EnumDecl:
            handle_container_decl(cursor, ENUM_TYPE);
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
                parent_kind == CXCursor_StructDecl || parent_kind == CXCursor_ClassDecl || parent_kind ==
                CXCursor_UnionDecl,
                "parent is not struct/class declaration");

            const CXType parent_type = clang_getCursorType(parent);
            if (!type_declared(parent_type))
                clang_visitChildren(cursor, visit_cursor, nullptr);

            nlohmann::json &parent_structure = get_type_json(parent_type);
            auto &members = parent_structure["members"];

            const CXString name = clang_getCursorSpelling(cursor);
            nlohmann::json member_info = {};
            member_info["name"] = clang_getCString(name);

            if (!parent_structure.contains("isUnion")) {
                const auto bit_offset = clang_Cursor_getOffsetOfField(cursor);
                member_info["offset"] = bit_offset / 8;

                if (clang_Cursor_isBitField(cursor)) {
                    member_info["bitOffset"] = bit_offset % 8;
                    member_info["bitSize"] = clang_getFieldDeclBitWidth(cursor);
                }
            }

            const CXType field_type = clang_getCursorType(cursor);
            if (field_type.kind == CXType_ConstantArray) {
                member_info["type"] = normalize_field_type_name(clang_getArrayElementType(field_type));
                member_info["arrsize"] = clang_getArraySize(field_type);
            } else {
                member_info["type"] = normalize_field_type_name(field_type);
            }

            members.push_back(member_info);
            clang_disposeString(name);
            break;
        }
        case CXCursor_TypedefDecl: {
            const CXString typedef_name = clang_getCursorSpelling(cursor);
            const CXType underlying_type = clang_getTypedefDeclUnderlyingType(cursor);

            auto name = clang_getCString(typedef_name);
            auto type = normalize_field_type_name(underlying_type);

            if (name != type) {
                nlohmann::json type_info;
                type_info["name"] = name;
                type_info["type"] = type;

                insert_type_declared(clang_getCursorType(cursor), type_info, TYPEDEF_TYPE);
            }

            clang_disposeString(typedef_name);
        }

        case CXCursor_ClassTemplate: {
            // return CXChildVisit_Continue;
        }
    }

    return CXChildVisit_Recurse;
}

int main(const int argc, char **argv) {
    if (argc < 2) {
        std::cout << "Target header paths has not been specified" << std::endl;
        return -1;
    }

    // setup stub file
    const std::filesystem::path current_path = std::filesystem::current_path();
    const auto stub_source = current_path / "stub_include.c";

    // setup arguments
    const std::vector<std::string> clang_args =
    {
        // "-I" + std::string(argv[1]),
        "-x", "c++",
        "-target x86_64-windows-msvc",
        "-fms-extensions",
        "-Xclang",
        "-ast-dump",
        "-fsyntax-only",
    };

    std::vector<const char *> c_args;
    for (const auto &arg: clang_args)
        c_args.push_back(arg.c_str());

    const std::vector<std::string> target_headers = {
        "phnt.h"
    };

    std::ofstream include_stub(stub_source, std::ios::out | std::ios::trunc);
    for (auto &include: target_headers)
        include_stub << std::format("#include <{}>\n", include);

    include_stub.close();

    if (const auto index = clang_createIndex(0, 1)) {
        CXTranslationUnit tu = nullptr;
        const auto error = clang_parseTranslationUnit2(
            index,
            stub_source.string().c_str(),
            c_args.data(),
            static_cast<int>(c_args.size()),
            nullptr,
            0,
            CXTranslationUnit_DetailedPreprocessingRecord | CXTranslationUnit_PrecompiledPreamble |
            CXTranslationUnit_SkipFunctionBodies,
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

    // std::vector<std::string> decl_order;
    // std::unordered_map<std::string, std::pair<json_category, nlohmann::json *> > name_mapping;
    //
    // for (auto &val: declared_types | std::views::values) {
    //     auto &[body, type] = val;
    //     switch (type) {
    //         case UNION_TYPE:
    //         case STRUCT_TYPE:
    //             name_mapping[body["name"]] = {type, &body};
    //             break;
    //     }
    // }
    //
    // auto dfs = [](nlohmann::json *val) {
    //     auto json_val = *val;
    //     auto members = json_val["members"];
    //
    //     for (nlohmann::json member: members) {
    //     }
    // };

    nlohmann::json root_type_object;
    root_type_object["structs"] = {};
    root_type_object["unions"] = {};
    root_type_object["types"] = {};
    root_type_object["enums"] = {};

    for (auto &val: declared_types | std::views::values) {
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
        }
    }

    std::ofstream out("windows_types_x64.json", std::ios::trunc);
    out << root_type_object.dump(4) << std::endl;

    return EXIT_SUCCESS;
}
