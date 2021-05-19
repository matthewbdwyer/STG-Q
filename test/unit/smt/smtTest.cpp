#define CATCH_CONFIG_MAIN
#include "catch.hpp"

#include <iostream>
#include <optional>
#include "Constraint.h"
#include "SMTPrinter.h"


std::string helper(std::stringstream &stream){

    std::stringstream outputStream;
    std::optional<std::shared_ptr<Constraints>> ast;

    REQUIRE_NOTHROW(ast = Constraint::parse(stream));
    
    std::string stgq_home_path = std::string(std::getenv("STGQ_HOME"));
    std::string dict_path = stgq_home_path+"/test/unit/smt/dict.json";
    const char *dict = dict_path.c_str(); 

    SMTPrinter smtp(outputStream, 2);
    smtp.print(ast.value(), dict);

    std::string output = outputStream.str();

    return output;
}


TEST_CASE("FXP Table: locals", "[SMT_Dict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (oeq X_float X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("(declare-const X_float Real)");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("No_var", "[No_var]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (oeq (float 1.0) (float 2.0))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("(= 1 0)");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("No_data", "[FXP_Dict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (oeq X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("No data available for: X");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("No_range", "[FXP_Dict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_no_range : float
        ]

        (oeq X_no_range X_no_range)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("No Range available for: X_no_range");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("No_max", "[FXP_Dict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_no_max : float
        ]

        (oeq X_no_max X_no_max)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("No Max value available for: X_no_max");
    REQUIRE(found!=std::string::npos);
}

TEST_CASE("No_min", "[FXP_Dict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_no_min : float
        ]

        (oeq X_no_min X_no_min)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("No min value available");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("No_distrib", "[FXP_Dict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_no_distrib : i8
        ]

        (eq X_no_distrib X_no_distrib)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("UniformInt");
    REQUIRE(found!=std::string::npos);
}

TEST_CASE("No_distrib2", "[FXP_Dict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_no_distrib_float : float
        ]

        (oeq X_no_distrib_float X_no_distrib_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("UniformReal");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("Invalid_distrib", "[FXP_Dict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_geo : float
        ]

        (oeq X_geo X_geo)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("Only Uniform distribution currently available");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("Binary_var", "[Binary_var]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_bin : i1
        ]

        (eq X_bin X_bin)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("(declare-const X_bin Bool)");
    REQUIRE(found!=std::string::npos);
}



TEST_CASE("Boolean_constant", "[Int]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_bin : i1
        ]

        (eq (i1 1) (i1 0))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("true");
    REQUIRE(found!=std::string::npos);

    found = output.find("false");
    REQUIRE(found!=std::string::npos);
}



TEST_CASE("Int_constant", "[Int]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i32
        ]

        (eq (i32 10) X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("10");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("Double_const", "[Double]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_double : double
        ]

        (oeq (double 1.5) X_double)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("1.5");
    REQUIRE(found!=std::string::npos);
}



TEST_CASE("fneg", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (oeq X_float (fneg X_float))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("-X_float");
    REQUIRE(found!=std::string::npos);
}

TEST_CASE("trunc_int", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (eq X_int (trunc i8 (i16 5)))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("= X_int 5");
    REQUIRE(found!=std::string::npos);
}

// TEST_CASE("trunc_bool", "[Unary_Intrinsic]") {
//     std::stringstream stream;
//     stream << R"(
    
//         [
//             X_bin : i1
//         ]

//         (eq X_bin (trunc i1 (i16 1)))

//     )";

//     std::string output = helper(stream);

//     std::size_t found = output.find("((_ sfxp 0) #x00000000");
//     REQUIRE(found!=std::string::npos);
// }

// TEST_CASE("trunc_float", "[Unary_Intrinsic]") {
//     std::stringstream stream;
//     stream << R"(
    
//         [
//             X_float : float
//         ]

//         (eq X_float (fptrunc float (double 1.0)))

//     )";

//     std::string output = helper(stream);

//     std::size_t found = output.find("((_ sfxp 5) #b0000");
//     REQUIRE(found!=std::string::npos);
// }



TEST_CASE("no_key", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (oeq X_float (neg X_float))

    )";

    std::string output;

    REQUIRE_THROWS_WITH(output = helper(stream), "bad optional access");
}



TEST_CASE("add", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8,
            Y_int : i8
        ]

        (sgt (add X_int Y_int) X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("+ X_int Y_int");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("sub", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8,
            Y_int : i8
        ]

        (sgt (sub X_int Y_int) X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("- X_int Y_int");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("mul", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8,
            Y_int : i8
        ]

        (sgt (mul X_int Y_int) X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("* X_int Y_int");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("sdiv", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8,
            Y_int : i8
        ]

        (sgt (sdiv X_int Y_int) X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("/ X_int Y_int");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("srem", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (eq (srem X_int (i8 2)) X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("% X_int 2");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("fadd", "[Binary_float_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float,
            Y_float : float
        ]

        (ogt (fadd X_float Y_float) X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("+ X_float Y_float");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("fsub", "[Binary_float_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float,
            Y_float : float
        ]

        (ogt (fsub X_float Y_float) X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("- X_float Y_float");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("fmul", "[Binary_float_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float,
            Y_float : float
        ]

        (ogt (fmul X_float Y_float) X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("* X_float Y_float");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("fdiv", "[Binary_float_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float,
            Y_float : float
        ]

        (oeq (fdiv X_float Y_float) X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("/ X_float Y_float");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("invalid_key", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8,
            Y_int : i8
        ]

        (sgt (ad X_int Y_int) X_int)

    )";

    std::string output;

    REQUIRE_THROWS_WITH(output = helper(stream), "bad optional access");

}


TEST_CASE("frem", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (oeq (frem X_float (float 2.0)) X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("% X_float 2.0");
    REQUIRE(found!=std::string::npos);

}


// Comparison

TEST_CASE("eq", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (eq X_int X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("= X_int X_int");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("ne", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (ne X_int X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("not(= X_int X_int");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("slt", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (slt X_int X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("< X_int X_int");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("sle", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (sle X_int X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("<= X_int X_int");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("sgt", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (sgt X_int X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("> X_int X_int");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("sge", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (sge X_int X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find(">= X_int X_int");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("oeq", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (oeq X_float X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("= X_float X_float");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("one", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (one X_float X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("not(= X_float X_float");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("olt", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (olt X_float X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("< X_float X_float");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("ole", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (ole X_float X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("<= X_float X_float");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("ogt", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (ogt X_float X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("> X_float X_float");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("oge", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (oge X_float X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find(">= X_float X_float");
    REQUIRE(found!=std::string::npos);

}

/*
TEST_CASE("ult", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (ult X_int X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ufxp.lt X_int X_int");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("ule", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (ule X_int X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ufxp.leq X_int X_int");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("ugt", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (ugt X_int X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ufxp.gt X_int X_int");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("uge", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (uge X_int X_int)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ufxp.geq X_int X_int");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("fult", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (fult X_float X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ufxp.lt X_float X_float");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("fule", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (fule X_float X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ufxp.leq X_float X_float");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("fugt", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (fugt X_float X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ufxp.gt X_float X_float");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("fuge", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (fuge X_float X_float)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ufxp.geq X_float X_float");
    REQUIRE(found!=std::string::npos);

}
*/

// Boolean comparison


TEST_CASE("land", "[Boolean_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (land (eq X_int X_int) (ne X_int X_int))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("and (= X_int X_int) (not(= X_int X_int))");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("lor", "[Boolean_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (or (eq X_int X_int) (ne X_int X_int))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("or (= X_int X_int) (not(= X_int X_int))");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("lnot", "[Boolean_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (lnot (eq X_int X_int))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("not (= X_int X_int)");
    REQUIRE(found!=std::string::npos);

}

/*
TEST_CASE("xor", "[Boolean_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (xor (eq X X) (ne X X))

    )";

    std::stringstream outputStream;
    std::optional<std::shared_ptr<Constraints>> ast;
    REQUIRE_NOTHROW(ast = Constraint::parse(stream));

    QCoralPrinter qcp(outputStream, 2);
    qcp.print(ast.value(), NULL);

    std::string output = outputStream.str();

    std::size_t found = output.find("BXOR(IEQ(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

// Unary Intrinsics

TEST_CASE("sin", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (ole (fmul (llvm.sin.f32 double X) (fmul (llvm.sin.f64 double X) (fmul (llvm.sin.f80 double X) (fmul (llvm.sin.f128 double X) (sin double X))))  ) (double 1.0))

    )";

    std::stringstream outputStream;
    std::optional<std::shared_ptr<Constraints>> ast;
    REQUIRE_NOTHROW(ast = Constraint::parse(stream));

    QCoralPrinter qcp(outputStream, 2);
    qcp.print(ast.value(), NULL);

    std::string output = outputStream.str();

    std::size_t found = output.find("DLE(MUL(SIN_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("cos", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (ole (fmul (llvm.cos.f32 double X) (fmul (llvm.cos.f64 double X) (fmul (llvm.cos.f80 double X) (fmul (llvm.cos.f128 double X) (cos double X))))  ) (double 1.0))

    )";

    std::stringstream outputStream;
    std::optional<std::shared_ptr<Constraints>> ast;
    REQUIRE_NOTHROW(ast = Constraint::parse(stream));

    QCoralPrinter qcp(outputStream, 2);
    qcp.print(ast.value(), NULL);

    std::string output = outputStream.str();

    std::size_t found = output.find("DLE(MUL(COS_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("tan", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (ole (fmul (tan.f32 double X) (tan double X)) (double 1.0))

    )";

    std::stringstream outputStream;
    std::optional<std::shared_ptr<Constraints>> ast;
    REQUIRE_NOTHROW(ast = Constraint::parse(stream));

    QCoralPrinter qcp(outputStream, 2);
    qcp.print(ast.value(), NULL);

    std::string output = outputStream.str();

    std::size_t found = output.find("DLE(MUL(TAN_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("exp", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (ole (fmul (llvm.exp.f32 double X) (fmul (llvm.exp.f64 double X) (fmul (llvm.exp.f80 double X) (fmul (llvm.exp.f128 double X) (exp double X))))  ) (double 1.0))

    )";

    std::stringstream outputStream;
    std::optional<std::shared_ptr<Constraints>> ast;
    REQUIRE_NOTHROW(ast = Constraint::parse(stream));

    QCoralPrinter qcp(outputStream, 2);
    qcp.print(ast.value(), NULL);

    std::string output = outputStream.str();

    std::size_t found = output.find("DLE(MUL(EXP_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("log", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (ole (fmul (llvm.log.f32 double X) (fmul (llvm.log.f64 double X) (fmul (llvm.log.f80 double X) (fmul (llvm.log.f128 double X) (log double X))))  ) (double 1.0))

    )";

    std::stringstream outputStream;
    std::optional<std::shared_ptr<Constraints>> ast;
    REQUIRE_NOTHROW(ast = Constraint::parse(stream));

    QCoralPrinter qcp(outputStream, 2);
    qcp.print(ast.value(), NULL);

    std::string output = outputStream.str();

    std::size_t found = output.find("DLE(MUL(LOG_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("log10", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (ole (fmul (llvm.log10.f32 double X) (fmul (llvm.log10.f64 double X) (fmul (llvm.log10.f80 double X) (fmul (llvm.log10.f128 double X) (log10f double X))))  ) (double 1.0))

    )";

    std::stringstream outputStream;
    std::optional<std::shared_ptr<Constraints>> ast;
    REQUIRE_NOTHROW(ast = Constraint::parse(stream));

    QCoralPrinter qcp(outputStream, 2);
    qcp.print(ast.value(), NULL);

    std::string output = outputStream.str();

    std::size_t found = output.find("DLE(MUL(LOG10_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

*/


TEST_CASE("sqrt", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (ole (fmul (llvm.sqrt.f32 double X_float) (fmul (llvm.sqrt.f64 double X_float) (fmul (llvm.sqrt.f80 double X_float) (fmul (llvm.sqrt.f128 double X_float) (sqrt double X_float))))  ) (double 1.0))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("^");
    REQUIRE(found!=std::string::npos);

    found = output.find("0.5");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("exp2", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (ole (fmul (llvm.exp2.f32 double X_float) (fmul (llvm.exp2.f64 double X_float) (fmul (llvm.exp2.f80 double X_float) (llvm.exp2.f128 double X_float)))  ) (double 1.0))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("^ 2.0");
    REQUIRE(found!=std::string::npos);

}

// Binary Intrinsics

TEST_CASE("pow", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_double : double
        ]

        (ole (fmul (llvm.pow.f32 double X_double (double 2.0)) (fmul (llvm.pow.f64 double X_double (double 2.0)) (fmul (llvm.pow.f80 double X_double (double 2.0)) (fmul (llvm.pow.f128 double X_double (double 2.0)) (pow double X_double (double 2.0)))))  ) (double 1.0))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("^");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("minnum", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_double : double
        ]

        (ole (fmul (llvm.minnum.f32 double X_double X_double) (fmul (llvm.minnum.f64 double X_double X_double) (fmul (llvm.minnum.f80 double X_double X_double) (llvm.minnum.f128 double X_double X_double)))  ) X_double)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("min");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("minimum", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_double : double
        ]

        (ole (fmul (llvm.minimum.f32 double X_double X_double) (fmul (llvm.minimum.f64 double X_double X_double) (fmul (llvm.minimum.f80 double X_double X_double) (llvm.minimum.f128 double X_double X_double)))  ) X_double)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("min");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("maxnum", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_double : double
        ]

        (ole (fmul (llvm.maxnum.f32 double X_double X_double) (fmul (llvm.maxnum.f64 double X_double X_double) (fmul (llvm.maxnum.f80 double X_double X_double) (llvm.maxnum.f128 double X_double X_double)))  ) X_double)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("max");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("maximum", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_double : double
        ]

        (ole (fmul (llvm.maximum.f32 double X_double X_double) (fmul (llvm.maximum.f64 double X_double X_double) (fmul (llvm.maximum.f80 double X_double X_double) (llvm.maximum.f128 double X_double X_double)))  ) X_double)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("max");
    REQUIRE(found!=std::string::npos);

}
/*
TEST_CASE("atan2", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (ole (fmul (atan2.f32 float X X) (atan2 float X X)) X)

    )";

    std::stringstream outputStream;
    std::optional<std::shared_ptr<Constraints>> ast;
    REQUIRE_NOTHROW(ast = Constraint::parse(stream));

    QCoralPrinter qcp(outputStream, 2);
    qcp.print(ast.value(), NULL);

    std::string output = outputStream.str();

    std::size_t found = output.find("DLE(MUL(ATAN2_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

*/