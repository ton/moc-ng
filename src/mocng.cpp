/****************************************************************************
 * Copyright (C) 2012 Woboq UG (haftungsbeschraenkt)
 * Olivier Goffart <contact at woboq.com>
 * http://woboq.com/
 ****************************************************************************/

#include "mocng.h"
#include "propertyparser.h"

#include <clang/Lex/Preprocessor.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/DeclTemplate.h>
#include <clang/AST/Type.h>
#include <clang/Sema/Sema.h>
#include <clang/Sema/Lookup.h>

#include <iostream>

static clang::SourceLocation GetFromLiteral(clang::Token Tok, clang::StringLiteral *Lit, clang::Preprocessor &PP) {
    return Lit->getLocationOfByte(PP.getSourceManager().getFileOffset(Tok.getLocation()),
                           PP.getSourceManager(), PP.getLangOpts(), PP.getTargetInfo());
}


static void parseEnums(ClassDef &Def, bool isFlag, clang::Expr *Content, clang::Sema &Sema) {
    clang::Preprocessor &PP = Sema.getPreprocessor();
    clang::StringLiteral *Val = llvm::dyn_cast<clang::StringLiteral>(Content);
    if (!Val) {
        PP.getDiagnostics().Report(Content->getExprLoc(),
                                   PP.getDiagnostics().getCustomDiagID(clang::DiagnosticsEngine::Error,
                                   "Invalid Q_ENUMS annotation"));
        return;
    }

    llvm::MemoryBuffer* Buf = llvm::MemoryBuffer::getMemBufferCopy(Val->getString(), "Q_PROPERTY");
    clang::Lexer Lex(PP.getSourceManager().createFileIDForMemBuffer(Buf, clang::SrcMgr::C_User, 0, 0, Content->getExprLoc()),
                     Buf, PP.getSourceManager(), PP.getLangOpts());

    clang::CXXScopeSpec SS;
    clang::Token Tok, Next;
    Lex.LexFromRawLexer(Tok);
    for (; !Tok.is(clang::tok::eof); Tok = Next) {
        Lex.LexFromRawLexer(Next);
        clang::IdentifierInfo* II = nullptr;
        if (Tok.is(clang::tok::raw_identifier))
            II = PP.LookUpIdentifierInfo(Tok);


        if (Tok.is(clang::tok::identifier)) {

            if (Next.is(clang::tok::coloncolon)) {
                if (Sema.ActOnCXXNestedNameSpecifier(Sema.getScopeForContext(Def.Record), *II,
                        GetFromLiteral(Tok, Val, PP), GetFromLiteral(Next, Val, PP), {}, false, SS))
                    SS.SetInvalid({GetFromLiteral(Tok, Val, PP), GetFromLiteral(Next, Val, PP)});

                Lex.LexFromRawLexer(Next);
                continue;
            }

            clang::LookupResult Found(Sema, II, GetFromLiteral(Tok, Val, PP), clang::Sema::LookupNestedNameSpecifierName);
            if (SS.isEmpty())
                Sema.LookupQualifiedName(Found, Def.Record);
            else {
                clang::DeclContext* DC = Sema.computeDeclContext(SS);
                Sema.LookupQualifiedName(Found, DC ? DC : Def.Record);
            }

            std::string Alias;
            clang::EnumDecl* R = Found.getAsSingle<clang::EnumDecl>();

            if (!R) {
                if (clang::TypedefDecl *TD = Found.getAsSingle<clang::TypedefDecl>()) {
                    const clang::EnumType* ET = TD->getUnderlyingType()->getAs<clang::EnumType>();
                    const clang::TemplateSpecializationType* TDR = TD->getUnderlyingType()->getAs<clang::TemplateSpecializationType>();
                    if(TDR && TDR->getNumArgs() == 1 && TDR->getTemplateName().getAsTemplateDecl()->getName() == "QFlags")
                        ET = TDR->getArg(0).getAsType()->getAs<clang::EnumType>();
                    if (ET) {
                        R = ET->getDecl();
                        Alias = TD->getNameAsString();
                    }
                }
            }

            if (Found.empty() || !R) {
                // TODO: typo correction

                // This should be an error, but the official moc do not understand that as an error.
                PP.getDiagnostics().Report(GetFromLiteral(Tok, Val, PP),
                                           PP.getDiagnostics().getCustomDiagID(clang::DiagnosticsEngine::Warning,
                                            "no enum names %0")) << Found.getLookupName();
                break;
            }
            if (R->getDeclContext() == Def.Record)
                Def.addEnum(R, Alias.empty() ? R->getNameAsString() : Alias, isFlag);
            else if (R->getDeclContext()->isRecord() &&  llvm::isa<clang::CXXRecordDecl>(R->getDeclContext())) {
                // TODO: check it is a QObject
                Def.addExtra(llvm::cast<clang::CXXRecordDecl>(R->getDeclContext()));
            }
            continue;
        } else if (Tok.is(clang::tok::coloncolon)) {
            if (SS.isEmpty()) {
                SS.MakeGlobal(Sema.getASTContext(), GetFromLiteral(Tok, Val, PP));
                continue;
            }
        }

        PP.getDiagnostics().Report(GetFromLiteral(Tok, Val, PP),
                                       PP.getDiagnostics().getCustomDiagID(clang::DiagnosticsEngine::Error,
                                       "Invalid token in Q_ENUMS"));
        break;
    }


}

ClassDef parseClass (clang::CXXRecordDecl *RD, clang::Sema &Sema) {
    clang::Preprocessor &PP = Sema.getPreprocessor();
    ClassDef Def;
    Def.Record = RD;

    for (auto it = RD->decls_begin(); it != RD->decls_end(); ++it) {
        if (clang::StaticAssertDecl *S = llvm::dyn_cast<clang::StaticAssertDecl>(*it) ) {
            if (auto *E = llvm::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(S->getAssertExpr()))
                if (clang::ParenExpr *PE = llvm::dyn_cast<clang::ParenExpr>(E->getArgumentExpr()))
            {
                llvm::StringRef key = S->getMessage()->getString();
                if (key == "qt_property") {
                    clang::StringLiteral *Val = llvm::dyn_cast<clang::StringLiteral>(PE->getSubExpr());
                    if (Val) {
                        PropertyParser Parser(Val->getString(),
    //                                          Val->getStrTokenLoc(0),
                                            Val->getLocationOfByte(0, PP.getSourceManager(), PP.getLangOpts(), PP.getTargetInfo()),
                                            Sema, Def.Record);
                        Def.Properties.push_back(Parser.parse());
                        Def.addExtra(Parser.Extra);
                    } else {
                        PP.getDiagnostics().Report(S->getLocation(),
                                                   PP.getDiagnostics().getCustomDiagID(clang::DiagnosticsEngine::Error,
                                                   "Invalid Q_PROPERTY annotation"));
                    }
                } else if (key == "qt_enums")  {
                    parseEnums(Def, false, PE->getSubExpr(), Sema);
                } else if (key == "qt_flags")  {
                    parseEnums(Def, true, PE->getSubExpr(), Sema);
                } else if (key == "qt_qobject") {
                    Def.HasQObject = true;
                } else if (key == "qt_qgadget") {
                    Def.HasQGadget = true;
                } else if (key == "qt_classinfo") {
                    clang::BinaryOperator* BO = llvm::dyn_cast<clang::BinaryOperator>(PE->getSubExpr());
                    clang::StringLiteral *Val1 = nullptr, *Val2 = nullptr;
                    if (!BO) {
                        PP.getDiagnostics().Report(S->getLocation(),
                                                   PP.getDiagnostics().getCustomDiagID(clang::DiagnosticsEngine::Error,
                                                   "Invalid Q_CLASSINFO annotation"));
                    } else {
                        if (!(Val1 = llvm::dyn_cast<clang::StringLiteral>(BO->getLHS())))
                            PP.getDiagnostics().Report(BO->getLHS()->getExprLoc(),
                                                       PP.getDiagnostics().getCustomDiagID(clang::DiagnosticsEngine::Error,
                                                       "Expected string literal in Q_CLASSINFO"));
                        if (!(Val2 = llvm::dyn_cast<clang::StringLiteral>(BO->getRHS())))
                            PP.getDiagnostics().Report(BO->getRHS()->getExprLoc(),
                                                        PP.getDiagnostics().getCustomDiagID(clang::DiagnosticsEngine::Error,
                                                        "Expected string literal in Q_CLASSINFO"));
                    }
                    if (Val1 && Val2) {
                        Def.ClassInfo.emplace_back(Val1->getString(), Val2->getString());
                    }
                }
            }
        } else if (clang::CXXMethodDecl *M = llvm::dyn_cast<clang::CXXMethodDecl>(*it)) {
       // int Clones = it->getNumParams() - it->getMinRequiredArguments();
            for (auto attr_it = M->specific_attr_begin<clang::AnnotateAttr>();
                attr_it != M->specific_attr_end<clang::AnnotateAttr>();
                ++attr_it) {

                const clang::AnnotateAttr *A = *attr_it;
                if (A->getAnnotation() == "qt_signal") {
            //        for (int i = 0; i < Clones; ++i)
                        Def.Signals.push_back(M);
                } else if (A->getAnnotation() == "qt_slot") {
        //         for (int i = 0; i < Clones; ++i)
                        Def.Slots.push_back(M);
                } else if (A->getAnnotation() == "qt_invokable") {
                    if (auto *C = llvm::dyn_cast<clang::CXXConstructorDecl>(M)) {
            //            for (int i = 0; i < Clones; ++i)
                            Def.Constructors.push_back(C);
                    } else {
            //            for (int i = 0; i < Clones; ++i)
                            Def.Methods.push_back(M);
                    }
                }
            }
        }
    }
/*
    if (Def.HasQObject) {
        std::cout << Def.Record->getQualifiedNameAsString() <<  " is " << Def.HasQObject << "a Q_OBJECT" << std::endl;
    }*/


    //Check notify Signals
    for (PropertyDef &P: Def.Properties) {
        if (!P.notify.Str.empty()) {
            int Idx = 0;
            for (clang::CXXMethodDecl *MD : Def.Signals) {
                if (MD->getName() == P.notify.Str) {
                    P.notify.notifyId = Idx;
                    P.notify.MD = MD;
                    break;
                }
                Idx += 1 + MD->getNumParams() - MD->getMinRequiredArguments();
            }
            if (P.notify.notifyId < 0 ) {
                PP.getDiagnostics().Report(P.notify.Loc,
                        PP.getDiagnostics().getCustomDiagID(clang::DiagnosticsEngine::Error,
                        "NOTIFY signal '%0' of property '%1' does not exist in class %2"))
                    << P.notify.Str << P.name << Def.Record;
            } else {
                Def.NotifyCount++;
            }
        }

    }





    return Def;
}