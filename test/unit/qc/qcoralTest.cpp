#define CATCH_CONFIG_MAIN
#include "catch.hpp"

#include <iostream>
#include <optional>
#include "Constraint.h"
#include "QCoralPrinter.h"


std::string helper(std::stringstream &stream){

    std::stringstream outputStream;
    std::optional<std::shared_ptr<Constraints>> ast;
    REQUIRE_NOTHROW(ast = Constraint::parse(stream));

    QCoralPrinter qcp(outputStream, 2);
    qcp.print(ast.value(), NULL);

    std::string output = outputStream.str();

    return output;
}

std::string helper_dict(std::stringstream &stream){

    std::stringstream outputStream;
    std::optional<std::shared_ptr<Constraints>> ast;

    REQUIRE_NOTHROW(ast = Constraint::parse(stream));
    
    std::string stgq_home_path = std::string(std::getenv("STGQ_HOME"));
    std::string dict_path = stgq_home_path+"/test/unit/qcoral/dict.json";
    const char *dict = dict_path.c_str(); 

    QCoralPrinter qcp(outputStream, 2);
    qcp.print(ast.value(), dict);

    std::string output = outputStream.str();

    return output;
}

TEST_CASE("Qcoral Table: locals", "[QcoralDict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (oeq X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("1 UNIFORM_REAL");
    REQUIRE(found!=std::string::npos);

    // std::cout<<"Here is the op: \n"<< output<<"\n";

}

TEST_CASE("No_data_ints", "[QcoralDict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X1 : i16,
            X2 : i32,
            X3 : i64
        ]

        (land (eq X1 X1) (land (eq X2 X2) (eq X3 X3)))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("32,767");
    REQUIRE(found!=std::string::npos);

    found = output.find("1,000,000");
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

    std::size_t found = output.find("IEQ(ICONST(1), ICONST(0))");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("No_data", "[FXP_Dict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_no_data : float
        ]

        (oeq X_no_data X_no_data)

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("No data available for: X_no_data");
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

    std::string output = helper_dict(stream);

    std::size_t found = output.find("UNIFORM_REAL -1000000 1000000");
    REQUIRE(found!=std::string::npos);
}

TEST_CASE("No_range_ints", "[FXP_Dict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_no_range_i8 : i8,
            X_no_range_i16 : i16,
            X_no_range_i32 : i32,
            X_no_range_i64 : i64
        ]

        (land (eq X_no_range_i8 X_no_range_i8) 
            (land (eq X_no_range_i16 X_no_range_i16) 
                (land (eq X_no_range_i32 X_no_range_i32) (eq X_no_range_i64 X_no_range_i64))
            )
        )

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("UNIFORM_INT -128 127");
    REQUIRE(found!=std::string::npos);

    found = output.find("UNIFORM_INT -32768 32767");
    REQUIRE(found!=std::string::npos);

    found = output.find("UNIFORM_INT -1000000 1000000");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("No_distrib", "[FXP_Dict]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_no_distrib : i8,
            X_no_distrib_float: float
        ]

        (land (eq X_no_distrib X_no_distrib) (oeq X_no_distrib_float X_no_distrib_float) )

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("UNIFORM_INT");
    REQUIRE(found!=std::string::npos);

    found = output.find("UNIFORM_REAL");
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

    std::string output = helper_dict(stream);

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

    std::string output = helper_dict(stream);

    std::size_t found = output.find("No min value available for: X_no_min");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("Exponential_distrib", "[Distributions]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_exp_dis : float
        ]

        (oeq X_exp_dis X_exp_dis)

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("EXPONENTIAL");
    REQUIRE(found!=std::string::npos);
}

TEST_CASE("Exponential_distrib_no_mean", "[Distributions]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_exp_dis_no_mean : float
        ]

        (oeq X_exp_dis_no_mean X_exp_dis_no_mean)

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("No mean given for");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("Binomial_distrib", "[Distributions]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_bin_dis : float
        ]

        (oeq X_bin_dis X_bin_dis)

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("BINOMIAL");
    REQUIRE(found!=std::string::npos);
}

TEST_CASE("Binomial_distrib_insuff_params", "[Distributions]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_bin_dis_insuff_params : float
        ]

        (oeq X_bin_dis_insuff_params X_bin_dis_insuff_params)

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("A binomial variable requires num_trials and probability");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("Normal_distrib", "[Distributions]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_norm_dis : float
        ]

        (oeq X_norm_dis X_norm_dis)

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("NORMAL");
    REQUIRE(found!=std::string::npos);
}

TEST_CASE("Normal_distrib_insuff_params", "[Distributions]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_norm_dis_insuff_params : float
        ]

        (oeq X_norm_dis_insuff_params X_norm_dis_insuff_params)

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("A normal variable requires mean and standard deviation.");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("Geometric_distrib", "[Distributions]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_geo : float
        ]

        (oeq X_geo X_geo)

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("GEOMETRIC");
    REQUIRE(found!=std::string::npos);
}

TEST_CASE("Geometric_distrib_no_probab", "[Distributions]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_geo_no_probab : float
        ]

        (oeq X_geo_no_probab X_geo_no_probab)

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("No probability given for");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("Poisson_distrib", "[Distributions]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_poi_dis : float
        ]

        (oeq X_poi_dis X_poi_dis)

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("POISSON");
    REQUIRE(found!=std::string::npos);
}

TEST_CASE("Poisson_distrib_no_lambda", "[Distributions]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_poi_dis_no_lam : float
        ]

        (oeq X_poi_dis_no_lam X_poi_dis_no_lam)

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("No lambda given for");
    REQUIRE(found!=std::string::npos);
}

TEST_CASE("Invalid_distrib", "[Distributions]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_beta_distrib : float
        ]

        (oeq X_beta_distrib X_beta_distrib)

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("Invalid distribution for");
    REQUIRE(found!=std::string::npos);
}

TEST_CASE("Bool_const", "[Bool]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (land (i1 0) (oeq X_float X_float))

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("IEQ(ICONST(1), ICONST(0))");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("trunc_zero", "[Trunc]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (land (oeq X_float X_float) (trunc i1 (i8 0)))

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("IEQ(ICONST(1), ICONST(0))");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("trunc_one", "[Trunc]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_float : float
        ]

        (land (oeq X_float X_float) (trunc i1 (i8 1)))

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("IEQ(ICONST(1), ICONST(1))");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("trunc_int", "[Trunc]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (land (i1 1) (trunc i1 X_int))

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("Trunc operation on IVAR(id_");
    REQUIRE(found!=std::string::npos);
}



TEST_CASE("zext_zero", "[Zext]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (eq X_int (zext i8 (i1 0)))

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("ICONST(0)");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("zext_one", "[Zext]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (eq X_int (zext i8 (i1 1)))

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("ICONST(1)");
    REQUIRE(found!=std::string::npos);
}


TEST_CASE("zext_int", "[Zext]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X_int : i8
        ]

        (eq (i16 1) (zext i16 X_int))

    )";

    std::string output = helper_dict(stream);

    std::size_t found = output.find("ASINT(IVAR(id_");
    REQUIRE(found!=std::string::npos);
}



TEST_CASE("fneg", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (oeq X (fneg X))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("MUL(DVAR(id_");
    REQUIRE(found!=std::string::npos);

    found = output.find("DCONST(-1)");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("fptosi", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (eq (i8 1) (fptosi i8 X))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ASINT(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("sitofp", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (oeq (float 1.0) (sitofp float X))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ASDOUBLE(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("add", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8,
            Y : i8
        ]

        (sgt (add X Y) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ADD(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("sub", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8,
            Y : i8
        ]

        (sgt (sub X Y) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("SUB(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("mul", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8,
            Y : i8
        ]

        (sgt (mul X Y) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("MUL(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("sdiv", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (eq (sdiv X (i8 1)) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DIV(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("srem", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (eq (srem X (i8 2)) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ASINT(MOD(ASDOUBLE(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("fadd", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float,
            Y : float
        ]

        (ogt (fadd X Y) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ADD(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("fsub", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float,
            Y : float
        ]

        (ogt (fsub X Y) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("SUB(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("fmul", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float,
            Y : float
        ]

        (ogt (fmul X Y) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("MUL(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("fdiv", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (oeq (fdiv X (float 1.0)) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DIV(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("frem", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (oeq (frem X (float 2.0)) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("MOD(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}


// Comparison

TEST_CASE("eq", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (eq X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("IEQ(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("ne", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (ne X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("INE(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("slt", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (slt X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ILT(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("sle", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (sle X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("ILE(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("sgt", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (sgt X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("IGT(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("sge", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (sge X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("IGE(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}


TEST_CASE("oeq", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (oeq X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DEQ(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("one", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (one X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DNE(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("olt", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (olt X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DLT(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("ole", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (ole X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DLE(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("ogt", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (ogt X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DGT(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("oge", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (oge X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DGE(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("ult", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (ult X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("BOR(BAND(IGE(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("ugt", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (ugt X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("BOR(BAND(IGE(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("fult", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (fult X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("BOR(BAND(DGE(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("fugt", "[Binary_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (fugt X X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("BOR(BAND(DGE(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

// Boolean comparison


TEST_CASE("land", "[Boolean_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (land (eq X X) (ne X X))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("BAND(IEQ(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("lor", "[Boolean_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (lor (eq X X) (ne X X))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("BOR(IEQ(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("lnot", "[Boolean_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (lnot (eq X X))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("BNOT(IEQ(IVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("xor", "[Boolean_Comparison]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : i8
        ]

        (xor (eq X X) (ne X X))

    )";

    std::string output = helper(stream);

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

    std::string output = helper(stream);

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

    std::string output = helper(stream);

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

    std::string output = helper(stream);

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

    std::string output = helper(stream);

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

    std::string output = helper(stream);

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

    std::string output = helper(stream);

    std::size_t found = output.find("DLE(MUL(LOG10_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("sqrt", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (ole (fmul (llvm.sqrt.f32 double X) (fmul (llvm.sqrt.f64 double X) (fmul (llvm.sqrt.f80 double X) (fmul (llvm.sqrt.f128 double X) (sqrt double X))))  ) (double 1.0))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DLE(MUL(SQRT_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("exp2", "[Unary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (ole (fmul (llvm.exp2.f32 double X) (fmul (llvm.exp2.f64 double X) (fmul (llvm.exp2.f80 double X) (llvm.exp2.f128 double X)))  ) (double 1.0))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DLE(MUL(POW_(DCONST(2.0),DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

// Binary Intrinsics

TEST_CASE("pow", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : double
        ]

        (ole (fmul (llvm.pow.f32 double X (double 2.0)) (fmul (llvm.pow.f64 double X (double 2.0)) (fmul (llvm.pow.f80 double X (double 2.0)) (fmul (llvm.pow.f128 double X (double 2.0)) (pow double X (double 2.0)))))  ) (double 1.0))

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DLE(MUL(POW_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("minnum", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : double
        ]

        (ole (fmul (llvm.minnum.f32 double X X) (fmul (llvm.minnum.f64 double X X) (fmul (llvm.minnum.f80 double X X) (llvm.minnum.f128 double X X)))  ) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DLE(MUL(MIN_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("minimum", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : double
        ]

        (ole (fmul (llvm.minimum.f32 double X X) (fmul (llvm.minimum.f64 double X X) (fmul (llvm.minimum.f80 double X X) (llvm.minimum.f128 double X X)))  ) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DLE(MUL(MIN_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("maxnum", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : double
        ]

        (ole (fmul (llvm.maxnum.f32 double X X) (fmul (llvm.maxnum.f64 double X X) (fmul (llvm.maxnum.f80 double X X) (llvm.maxnum.f128 double X X)))  ) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DLE(MUL(MAX_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("maximum", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : double
        ]

        (ole (fmul (llvm.maximum.f32 double X X) (fmul (llvm.maximum.f64 double X X) (fmul (llvm.maximum.f80 double X X) (llvm.maximum.f128 double X X)))  ) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DLE(MUL(MAX_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}

TEST_CASE("atan2", "[Binary_Intrinsic]") {
    std::stringstream stream;
    stream << R"(
    
        [
            X : float
        ]

        (ole (fmul (atan2.f32 float X X) (atan2 float X X)) X)

    )";

    std::string output = helper(stream);

    std::size_t found = output.find("DLE(MUL(ATAN2_(DVAR(id_");
    REQUIRE(found!=std::string::npos);

}