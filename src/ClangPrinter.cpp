/*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "ClangPrinter.hpp"
#include "CoqPrinter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclCXX.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Mangle.h>
#include <clang/Basic/Version.h>
#include <clang/Frontend/CompilerInstance.h>

using namespace clang;

ClangPrinter::ClangPrinter(clang::CompilerInstance *compiler,
                           clang::ASTContext *context)
    : compiler_(compiler), context_(context) /*,
      engine_(IntrusiveRefCntPtr<DiagnosticIDs>(),
              IntrusiveRefCntPtr<DiagnosticOptions>()) */
{
    mangleContext_ =
        ItaniumMangleContext::create(*context, compiler->getDiagnostics());
}

clang::Sema &
ClangPrinter::getSema() const {
    return this->compiler_->getSema();
}

unsigned
ClangPrinter::getTypeSize(const BuiltinType *t) const {
    return this->context_->getTypeSize(t);
}

#if CLANG_VERSION_MAJOR >= 11
static GlobalDecl
to_gd(const NamedDecl *decl) {
    if (auto ct = dyn_cast<CXXConstructorDecl>(decl)) {
        return GlobalDecl(ct, CXXCtorType::Ctor_Complete);
    } else if (auto dt = dyn_cast<CXXDestructorDecl>(decl)) {
        return GlobalDecl(dt, CXXDtorType::Dtor_Deleting);
    } else {
        return GlobalDecl(decl);
    }
}
#else
static const NamedDecl *
to_gd(const NamedDecl *decl) {
    return decl;
}
#endif /* CLANG_VERSION_MAJOR >= 11 */

#ifdef STRUCTURED_NAMES
unsigned
getAnonymousIndex(const NamedDecl *here) {
    auto i = 0;
    for (auto x : here->getDeclContext()->decls()) {
        if (x == here)
            return i;
        break;
        if (auto ns = dyn_cast<NamespaceDecl>(x)) {
            if (ns->isAnonymousNamespace())
                ++i;
        } else if (auto r = dyn_cast<RecordDecl>(x)) {
            if (r->getIdentifier() == nullptr)
                ++i;
        } else if (auto e = dyn_cast<EnumDecl>(x)) {
            if (e->getIdentifier() == nullptr)
                ++i;
        }
    }
    assert(false && "didn't find declaration in its own DeclContext.");
}

void
ClangPrinter::printTypeName(const NamedDecl *here, CoqPrinter &print) {
    if (auto ts = dyn_cast<ClassTemplateSpecializationDecl>(here)) {
        print.ctor("Tspecialize");
        printTypeName(ts->getSpecializedTemplate(), print);
        print.output() << fmt::nbsp;
        auto &&args = ts->getTemplateArgs();
        print.begin_list();
        for (auto i = 0; i < args.size(); ++i) {
            auto &&arg = args[i];
            switch (arg.getKind()) {
            case TemplateArgument::ArgKind::Type:
                printQualType(arg.getAsType(), print);
                break;
            case TemplateArgument::ArgKind::Expression:
                printExpr(arg.getAsExpr(), print);
                break;
            case TemplateArgument::ArgKind::Integral:
                print.output() << arg.getAsIntegral().toString(10);
                break;
            case TemplateArgument::ArgKind::NullPtr:
                print.output() << "Enullptr";
                break;
            default:
                print.output() << "<else>";
            }
            print.cons();
        }
        print.end_list();
        print.end_ctor();
        return;
    }

    auto print_parent = [&](const DeclContext *parent) {
        if (auto pnd = dyn_cast<NamedDecl>(parent)) {
            printTypeName(pnd, print);
            print.output() << fmt::nbsp;
        } else {
            llvm::errs() << here->getDeclKindName() << "\n";
            assert(false && "unknown type in print_path");
        }
    };

    auto parent = here->getDeclContext();
    if (parent == nullptr or parent->isTranslationUnit()) {
        print.ctor("Qglobal", false);
        print.str(here->getName());
        print.end_ctor();
    } else if (auto nd = dyn_cast<NamespaceDecl>(here)) {
        print.ctor("Qnested", false);
        print_parent(parent);
        if (nd->isAnonymousNamespace() or nd->getIdentifier() == nullptr) {
            print.output() << "(Tanon " << getAnonymousIndex(nd) << ")";
        } else {
            print.str(here->getName());
        }
        print.end_ctor();
    } else if (auto rd = dyn_cast<RecordDecl>(here)) {
        print.ctor("Qnested", false);
        print_parent(parent);
        if (rd->getIdentifier() == nullptr) {
            print.output() << "(Tanon " << getAnonymousIndex(rd) << ")";
        } else {
            print.str(here->getName());
        }
        print.end_ctor();

    } else if (auto pnd = dyn_cast<NamedDecl>(parent)) {
        print.ctor("Qnested", false);
        printTypeName(pnd, print);
        print.output() << fmt::nbsp;
        print.str(here->getName());
        print.end_ctor();
    } else {
        llvm::errs() << here->getDeclKindName() << "\n";
        assert(false && "unknown type in print_path");
    }
}

void
ClangPrinter::printObjName(const NamedDecl *decl, CoqPrinter &print, bool raw) {
    if (!raw) {
        print.output() << "\"";
    }

    if (isa<RecordDecl>(decl)) {
#if 1
        if (auto RD = dyn_cast<CXXRecordDecl>(decl)) {
            if (auto dtor = RD->getDestructor()) {
                // HACK: this mangles an aggregate name by mangling
                // the destructor and then doing some string manipulation
                std::string sout;
                llvm::raw_string_ostream out(sout);
                mangleContext_->mangleName(to_gd(dtor), out);
                // the mangling of the destructor has the following form:
                // _ZN...DnEv -> _Z... [if the name is not compound]
                // _ZN...DnEv -> _ZN...E [if the name is compound]
                // compound names are ones with scopes or templates
                bool is_compound = true;
                // TODO
                if (is_compound) {
                    print.output() << sout.substr(0, sout.length() - 4) << "E";
                } else {
                    print.output()
                        << "_Z" << sout.substr(3, sout.length() - 4 - 3);
                }
            } else {
                print.output() << decl->getQualifiedNameAsString();
            }
        } else {
            assert(false);
        }
    } else if (auto ecd = dyn_cast<EnumConstantDecl>(decl)) {
        mangleContext_->mangleTypeName(ecd->getType(),
                                       print.output().nobreak());
        print.output() << "::" << ecd->getName();
#else
        decl->getNameForDiagnostic(print.output().nobreak(),
                                   PrintingPolicy(getContext().getLangOpts()),
                                   true);
#endif
    } else if (mangleContext_->shouldMangleDeclName(decl)) {
        mangleContext_->mangleName(to_gd(decl), print.output().nobreak());
    } else {
        print.output() << decl->getQualifiedNameAsString();
#if 0
        if (auto fd = dyn_cast<FunctionDecl>(decl)) {
            if (fd->getLanguageLinkage() == LanguageLinkage::CLanguageLinkage) {
                print.output() << fd->getNameAsString();
            } else {
                mangleContext_->mangleName(to_gd(fd), print.output().nobreak());
            }
        } else {
            mangleContext_->mangleName(to_gd(decl), print.output().nobreak());
        }
#endif
    }

    if (!raw) {
        print.output() << "\"";
    }
}

Optional<int>
ClangPrinter::getParameterNumber(const ParmVarDecl *decl) {
    assert(decl->getDeclContext()->isFunctionOrMethod() &&
           "function or method");
    if (auto fd = dyn_cast_or_null<FunctionDecl>(decl->getDeclContext())) {
        int i = 0;
        for (auto p : fd->parameters()) {
            if (p == decl)
                return Optional<int>(i);
            ++i;
        }
        llvm::errs() << "failed to find parameter\n";
    }
    return Optional<int>();
}

void
ClangPrinter::printParamName(const ParmVarDecl *decl, CoqPrinter &print) {
    auto name = decl->getIdentifier();
    print.output() << "\"";
    if (name == nullptr) {
        auto d = dyn_cast<ParmVarDecl>(decl);
        auto i = getParameterNumber(d);
        if (i.hasValue()) {
            print.output() << "#" << i;
        }
    } else {
        decl->printName(print.output().nobreak());
    }
    print.output() << "\"";
}

void
ClangPrinter::printName(const NamedDecl *decl, CoqPrinter &print) {
    if (decl->getDeclContext()->isFunctionOrMethod()) {
        print.ctor("Lname", false) << fmt::nbsp;
        auto name = decl->getNameAsString();
        if (auto pd = dyn_cast_or_null<ParmVarDecl>(decl)) {
            printParamName(pd, print);
        } else {
            print.output() << "\"" << decl->getNameAsString() << "\"";
        }
    } else {
        print.ctor("Gname", false);
        printObjName(decl, print);
    }
    print.output() << fmt::rparen;
}

void
ClangPrinter::printValCat(const Expr *d, CoqPrinter &print) {
#ifdef DEBUG
    d->dump(llvm::errs());
    llvm::errs().flush();
#endif
    // note(gmm): Classify doesn't work on dependent types which occur in templates
    // that clang can't completely eliminate.

    auto Class = d->Classify(*this->context_);
    if (Class.isLValue()) {
        print.output() << "Lvalue";
    } else if (Class.isXValue()) {
        print.output() << "Xvalue";
    } else if (Class.isPRValue()) {
        print.output() << "Prvalue";
    } else {
        assert(false);
        //fatal("unknown value category");
    }
}

void
ClangPrinter::printExprAndValCat(const Expr *d, CoqPrinter &print) {
    auto depth = print.output().get_depth();
    print.output() << fmt::lparen;
    printValCat(d, print);
    print.output() << "," << fmt::nbsp;
    printExpr(d, print);
    print.output() << fmt::rparen;
    assert(depth == print.output().get_depth());
}

void
ClangPrinter::printExprAndValCat(const Expr *d, CoqPrinter &print,
                                 OpaqueNames &li) {
    auto depth = print.output().get_depth();
    print.output() << fmt::lparen;
    printValCat(d, print);
    print.output() << "," << fmt::nbsp;
    printExpr(d, print, li);
    print.output() << fmt::rparen;
    assert(depth == print.output().get_depth());
}

void
ClangPrinter::printField(const ValueDecl *decl, CoqPrinter &print) {
    if (const FieldDecl *f = dyn_cast<clang::FieldDecl>(decl)) {
        print.ctor("Build_field", false);
        this->printTypeName(f->getParent(), print);
        print.output() << fmt::nbsp;

        if (decl->getName() == "") {
            const CXXRecordDecl *rd = f->getType()->getAsCXXRecordDecl();
            assert(rd && "unnamed field must be a record");
            print.ctor("Nanon", false);
            this->printGlobalName(rd, print);
            print.end_ctor();
        } else {
            print.str(decl->getName());
        }
        print.end_ctor();
    } else if (const CXXMethodDecl *meth =
                   dyn_cast<clang::CXXMethodDecl>(decl)) {
        print.ctor("Build_field", false);
        this->printGlobalName(meth->getParent(), print);
        print.output() << fmt::nbsp << "\"" << decl->getNameAsString() << "\"";
        print.end_ctor();
    } else if (const VarDecl *var = dyn_cast<VarDecl>(decl)) {

    } else {
        using namespace logging;
        fatal() << "member not pointing to field " << decl->getDeclKindName()
                << " (at " << sourceRange(decl->getSourceRange()) << ")\n";
        die();
    }
}

std::string
ClangPrinter::sourceRange(const SourceRange sr) const {
    return sr.printToString(this->context_->getSourceManager());
}

void
ClangPrinter::printCallingConv(clang::CallingConv cc, CoqPrinter &print) {
#define PRINT(x)                                                               \
    case CallingConv::x:                                                       \
        print.output() << #x;                                                  \
        break;
#define OVERRIDE(x, y)                                                         \
    case CallingConv::x:                                                       \
        print.output() << #y;                                                  \
        break;
    switch (cc) {
        PRINT(CC_C);
        OVERRIDE(CC_X86RegCall, CC_RegCall);
        OVERRIDE(CC_Win64, CC_MsAbi);
#if 0
        PRINT(CC_X86StdCall);
        PRINT(CC_X86FastCall);
        PRINT(CC_X86ThisCall);
        PRINT(CC_X86VectorCall);
        PRINT(CC_X86Pascal);
        PRINT(CC_X86_64SysV);
        PRINT(CC_AAPCS);
        PRINT(CC_AAPCS_VFP);
        PRINT(CC_IntelOclBicc);
        PRINT(CC_SpirFunction);
        PRINT(CC_OpenCLKernel);
        PRINT(CC_Swift);
        PRINT(CC_PreserveMost);
        PRINT(CC_PreserveAll);
        PRINT(CC_AArch64VectorCall);
#endif
    default:
        using namespace logging;
        logging::fatal() << "unsupported calling convention\n";
        logging::die();
    }
}
