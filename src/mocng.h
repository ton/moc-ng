/****************************************************************************
 *  Copyright (C) 2013-2016 Woboq GmbH
 *  Olivier Goffart <contact at woboq.com>
 *  https://woboq.com/
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#pragma once

#include <clang/Basic/SourceLocation.h>

#include <algorithm>
#include <iterator>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

#include "clangversionabstraction.h"
#include "qbjs.h"

class MocPPCallbacks;
namespace clang {
    class CXXMethodDecl;
    class CXXRecordDecl;
    class CXXConstructorDecl;
    class NamespaceDecl;
    class EnumDecl;
    class Preprocessor;
    class Sema;
    class TypeDecl;
    class Type;
    class QualType;
} // namespace clang

struct NotifyDef {
    std::string Str;
    clang::SourceLocation Loc;
    clang::CXXMethodDecl* MD = nullptr;
    int notifyId = -1;
};

struct PrivateSlotDef {
    std::string ReturnType;
    std::string Name;
    std::vector<std::string> Args;
    int NumDefault = 0;
    std::string InPrivateClass;
};

struct PropertyDef {
    std::string name, type, member, read, write, reset, designable = "true", scriptable = "true",
                                                        editable, stored = "true", user = "false",
                                                        inPrivateClass;
    NotifyDef notify;

    bool constant = false;
    bool final = false;

    bool isEnum = false;

    int revision = 0;
    bool PointerHack = false;             // If the READ method returns a pointer to the type
    bool PossiblyForwardDeclared = false; // if the type is only forward declared
};

struct PluginData {
    std::string IID;
    QBJS::Value MetaData;
};

struct BaseDef {
    std::vector<std::tuple<clang::EnumDecl*, std::string, bool>> Enums;

    void addEnum(clang::EnumDecl* E, std::string Alias, bool IsFlag)
    {
        for (auto I : Enums)
            if (std::get<1>(I) == Alias)
                return;

        Enums.emplace_back(E, std::move(Alias), IsFlag);
    }

    std::vector<clang::CXXRecordDecl*> Extra;
    void addExtra(clang::CXXRecordDecl* E)
    {
        if (!E)
            return;
        if (std::find(Extra.begin(), Extra.end(), E) != Extra.end())
            return;
        Extra.push_back(E);
    }

    std::vector<std::pair<std::string, std::string>> ClassInfo;
};

struct ClassDef : BaseDef {
    clang::CXXRecordDecl* Record = nullptr;

    // This list only includes the things registered with the keywords
    std::vector<clang::CXXMethodDecl*> Signals;
    std::vector<clang::CXXMethodDecl*> Slots;
    std::vector<PrivateSlotDef> PrivateSlots;
    std::vector<clang::CXXMethodDecl*> Methods;
    std::vector<clang::CXXConstructorDecl*> Constructors;

    std::vector<std::string> Interfaces;
    PluginData Plugin;

    std::vector<PropertyDef> Properties;

    bool HasQObject = false;
    bool HasQGadget = false;

    int NotifyCount = 0;
    int PrivateSlotCount = 0;
    int RevisionPropertyCount = 0;
    int RevisionMethodCount = 0;
};

struct NamespaceDef : BaseDef {
    clang::NamespaceDecl* Namespace = nullptr;
    bool hasQNamespace = false;
};

class MocNg {
  public:
    typedef std::set<const clang::Type*> MetaTypeSet;
    MetaTypeSet registered_meta_type;

    typedef std::unordered_map<std::string, const clang::CXXRecordDecl*> InterfaceMap;
    InterfaceMap interfaces;

    ClassDef parseClass(clang::CXXRecordDecl* RD, clang::Sema& Sema);
    NamespaceDef parseNamespace(clang::NamespaceDecl* ND, clang::Sema& Sema);

    bool HasPlugin = false;

    std::map<clang::SourceLocation, std::string> Tags;
    std::string GetTag(clang::SourceLocation DeclLoc, const clang::SourceManager& SM);
    bool ShouldRegisterMetaType(clang::QualType T);
};
