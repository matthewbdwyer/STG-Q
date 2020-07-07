; ModuleID = 'IPUT.bc'
source_filename = "if_else_if_else_min.cpp"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.14.0"

@.str = private unnamed_addr constant [42 x i8] c"among %d, %d, %d ,  minimum number is: %d\00", align 1
@.str.1 = private unnamed_addr constant [2 x i8] c"A\00", align 1
@.str.2 = private unnamed_addr constant [2 x i8] c"B\00", align 1
@.str.3 = private unnamed_addr constant [2 x i8] c"C\00", align 1
@prev_bb = global i8* getelementptr inbounds ([6 x i8], [6 x i8]* @132, i32 0, i32 0), align 4
@0 = private unnamed_addr constant [10 x i8] c"num1.addr\00", align 1
@1 = private unnamed_addr constant [10 x i8] c"num2.addr\00", align 1
@2 = private unnamed_addr constant [10 x i8] c"num3.addr\00", align 1
@3 = private unnamed_addr constant [4 x i8] c"min\00", align 1
@4 = private unnamed_addr constant [5 x i8] c"num1\00", align 1
@5 = private unnamed_addr constant [5 x i8] c"num2\00", align 1
@6 = private unnamed_addr constant [5 x i8] c"num3\00", align 1
@7 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_miniii\00", align 1
@8 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_miniii\00", align 1
@9 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii1\00", align 1
@10 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii1\00", align 1
@11 = private unnamed_addr constant [4 x i8] c"cmp\00", align 1
@12 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_miniii\00", align 1
@13 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii1\00", align 1
@14 = private unnamed_addr constant [4 x i8] c"slt\00", align 1
@15 = private unnamed_addr constant [4 x i8] c"i32\00", align 1
@16 = private unnamed_addr constant [4 x i8] c"cmp\00", align 1
@17 = private unnamed_addr constant [6 x i8] c"entry\00", align 1
@18 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii2\00", align 1
@19 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii2\00", align 1
@20 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii3\00", align 1
@21 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii3\00", align 1
@22 = private unnamed_addr constant [5 x i8] c"cmp1\00", align 1
@23 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii2\00", align 1
@24 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii3\00", align 1
@25 = private unnamed_addr constant [4 x i8] c"slt\00", align 1
@26 = private unnamed_addr constant [4 x i8] c"i32\00", align 1
@27 = private unnamed_addr constant [5 x i8] c"cmp1\00", align 1
@28 = private unnamed_addr constant [8 x i8] c"if.then\00", align 1
@29 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii4\00", align 1
@30 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii4\00", align 1
@31 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii4\00", align 1
@32 = private unnamed_addr constant [9 x i8] c"if.then2\00", align 1
@33 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii5\00", align 1
@34 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii5\00", align 1
@35 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii5\00", align 1
@36 = private unnamed_addr constant [8 x i8] c"if.else\00", align 1
@37 = private unnamed_addr constant [7 x i8] c"if.end\00", align 1
@38 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii6\00", align 1
@39 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii6\00", align 1
@40 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii7\00", align 1
@41 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii7\00", align 1
@42 = private unnamed_addr constant [5 x i8] c"cmp4\00", align 1
@43 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii6\00", align 1
@44 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii7\00", align 1
@45 = private unnamed_addr constant [4 x i8] c"slt\00", align 1
@46 = private unnamed_addr constant [4 x i8] c"i32\00", align 1
@47 = private unnamed_addr constant [5 x i8] c"cmp4\00", align 1
@48 = private unnamed_addr constant [9 x i8] c"if.else3\00", align 1
@49 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii8\00", align 1
@50 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii8\00", align 1
@51 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii8\00", align 1
@52 = private unnamed_addr constant [9 x i8] c"if.then5\00", align 1
@53 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii9\00", align 1
@54 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii9\00", align 1
@55 = private unnamed_addr constant [20 x i8] c"tmp__Z8find_miniii9\00", align 1
@56 = private unnamed_addr constant [9 x i8] c"if.else6\00", align 1
@57 = private unnamed_addr constant [8 x i8] c"if.end7\00", align 1
@58 = private unnamed_addr constant [21 x i8] c"tmp__Z8find_miniii10\00", align 1
@59 = private unnamed_addr constant [21 x i8] c"tmp__Z8find_miniii10\00", align 1
@60 = private unnamed_addr constant [21 x i8] c"tmp__Z8find_miniii11\00", align 1
@61 = private unnamed_addr constant [21 x i8] c"tmp__Z8find_miniii11\00", align 1
@62 = private unnamed_addr constant [21 x i8] c"tmp__Z8find_miniii12\00", align 1
@63 = private unnamed_addr constant [21 x i8] c"tmp__Z8find_miniii12\00", align 1
@64 = private unnamed_addr constant [21 x i8] c"tmp__Z8find_miniii13\00", align 1
@65 = private unnamed_addr constant [21 x i8] c"tmp__Z8find_miniii13\00", align 1
@66 = private unnamed_addr constant [21 x i8] c"tmp__Z8find_miniii14\00", align 1
@67 = private unnamed_addr constant [21 x i8] c"tmp__Z8find_miniii14\00", align 1
@68 = private unnamed_addr constant [19 x i8] c"_Z8find_miniii_RET\00", align 1
@69 = private unnamed_addr constant [21 x i8] c"tmp__Z8find_miniii14\00", align 1
@70 = private unnamed_addr constant [8 x i8] c"if.end8\00", align 1
@71 = private unnamed_addr constant [7 x i8] c"retval\00", align 1
@72 = private unnamed_addr constant [2 x i8] c"a\00", align 1
@73 = private unnamed_addr constant [2 x i8] c"b\00", align 1
@74 = private unnamed_addr constant [2 x i8] c"c\00", align 1
@75 = private unnamed_addr constant [8 x i8] c"(i32 0)\00", align 1
@76 = private unnamed_addr constant [9 x i8] c"tmp_main\00", align 1
@77 = private unnamed_addr constant [10 x i8] c"tmp_main1\00", align 1
@78 = private unnamed_addr constant [10 x i8] c"tmp_main2\00", align 1
@79 = private unnamed_addr constant [10 x i8] c"tmp_main3\00", align 1
@80 = private unnamed_addr constant [10 x i8] c"tmp_main4\00", align 1
@81 = private unnamed_addr constant [10 x i8] c"tmp_main5\00", align 1
@82 = private unnamed_addr constant [10 x i8] c"tmp_main6\00", align 1
@83 = private unnamed_addr constant [10 x i8] c"tmp_main6\00", align 1
@84 = private unnamed_addr constant [10 x i8] c"tmp_main7\00", align 1
@85 = private unnamed_addr constant [10 x i8] c"tmp_main7\00", align 1
@86 = private unnamed_addr constant [10 x i8] c"tmp_main8\00", align 1
@87 = private unnamed_addr constant [10 x i8] c"tmp_main8\00", align 1
@88 = private unnamed_addr constant [5 x i8] c"num1\00", align 1
@89 = private unnamed_addr constant [10 x i8] c"tmp_main6\00", align 1
@90 = private unnamed_addr constant [5 x i8] c"num2\00", align 1
@91 = private unnamed_addr constant [10 x i8] c"tmp_main7\00", align 1
@92 = private unnamed_addr constant [5 x i8] c"num3\00", align 1
@93 = private unnamed_addr constant [10 x i8] c"tmp_main8\00", align 1
@94 = private unnamed_addr constant [5 x i8] c"call\00", align 1
@95 = private unnamed_addr constant [19 x i8] c"_Z8find_miniii_RET\00", align 1
@96 = private unnamed_addr constant [10 x i8] c"tmp_main9\00", align 1
@97 = private unnamed_addr constant [11 x i8] c"tmp_main10\00", align 1
@98 = private unnamed_addr constant [11 x i8] c"tmp_main11\00", align 1
@99 = private unnamed_addr constant [11 x i8] c"tmp_main12\00", align 1
@100 = private unnamed_addr constant [11 x i8] c"tmp_main12\00", align 1
@101 = private unnamed_addr constant [11 x i8] c"tmp_main13\00", align 1
@102 = private unnamed_addr constant [11 x i8] c"tmp_main13\00", align 1
@103 = private unnamed_addr constant [11 x i8] c"tmp_main14\00", align 1
@104 = private unnamed_addr constant [11 x i8] c"tmp_main14\00", align 1
@105 = private unnamed_addr constant [5 x i8] c"num1\00", align 1
@106 = private unnamed_addr constant [11 x i8] c"tmp_main12\00", align 1
@107 = private unnamed_addr constant [5 x i8] c"num2\00", align 1
@108 = private unnamed_addr constant [11 x i8] c"tmp_main13\00", align 1
@109 = private unnamed_addr constant [5 x i8] c"num3\00", align 1
@110 = private unnamed_addr constant [11 x i8] c"tmp_main14\00", align 1
@111 = private unnamed_addr constant [6 x i8] c"call1\00", align 1
@112 = private unnamed_addr constant [19 x i8] c"_Z8find_miniii_RET\00", align 1
@113 = private unnamed_addr constant [11 x i8] c"tmp_main15\00", align 1
@114 = private unnamed_addr constant [11 x i8] c"tmp_main16\00", align 1
@115 = private unnamed_addr constant [11 x i8] c"tmp_main17\00", align 1
@116 = private unnamed_addr constant [11 x i8] c"tmp_main18\00", align 1
@117 = private unnamed_addr constant [11 x i8] c"tmp_main18\00", align 1
@118 = private unnamed_addr constant [11 x i8] c"tmp_main19\00", align 1
@119 = private unnamed_addr constant [11 x i8] c"tmp_main19\00", align 1
@120 = private unnamed_addr constant [11 x i8] c"tmp_main20\00", align 1
@121 = private unnamed_addr constant [11 x i8] c"tmp_main20\00", align 1
@122 = private unnamed_addr constant [5 x i8] c"num1\00", align 1
@123 = private unnamed_addr constant [11 x i8] c"tmp_main18\00", align 1
@124 = private unnamed_addr constant [5 x i8] c"num2\00", align 1
@125 = private unnamed_addr constant [11 x i8] c"tmp_main19\00", align 1
@126 = private unnamed_addr constant [5 x i8] c"num3\00", align 1
@127 = private unnamed_addr constant [11 x i8] c"tmp_main20\00", align 1
@128 = private unnamed_addr constant [6 x i8] c"call2\00", align 1
@129 = private unnamed_addr constant [19 x i8] c"_Z8find_miniii_RET\00", align 1
@130 = private unnamed_addr constant [9 x i8] c"main_RET\00", align 1
@131 = private unnamed_addr constant [2 x i8] c"0\00", align 1
@132 = private unnamed_addr constant [6 x i8] c"entry\00", align 1

; Function Attrs: noinline optnone ssp uwtable
define i32 @_Z8find_miniii(i32 %num1, i32 %num2, i32 %num3) #0 {
entry:
  %num1.addr = alloca i32, align 4
  %num2.addr = alloca i32, align 4
  %num3.addr = alloca i32, align 4
  %min = alloca i32, align 4
  store i32 %num1, i32* %num1.addr, align 4
  call void @stg_update_store(i32* %num1.addr, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @4, i32 0, i32 0))
  store i32 %num2, i32* %num2.addr, align 4
  call void @stg_update_store(i32* %num2.addr, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @5, i32 0, i32 0))
  store i32 %num3, i32* %num3.addr, align 4
  call void @stg_update_store(i32* %num3.addr, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @6, i32 0, i32 0))
  %tmp__Z8find_miniii = load i32, i32* %num1.addr, align 4
  call void @stg_update_load(i32* %num1.addr, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @8, i32 0, i32 0))
  %tmp__Z8find_miniii1 = load i32, i32* %num2.addr, align 4
  call void @stg_update_load(i32* %num2.addr, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @10, i32 0, i32 0))
  %cmp = icmp slt i32 %tmp__Z8find_miniii, %tmp__Z8find_miniii1
  call void @stg_update_cmp(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @11, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @12, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @14, i32 0, i32 0), i8* getelementptr inbounds ([20 x i8], [20 x i8]* @13, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @15, i32 0, i32 0))
  call void @stg_update_pc(i1 %cmp, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @16, i32 0, i32 0))
  br i1 %cmp, label %if.then, label %if.else3

if.then:                                          ; preds = %entry
  %tmp__Z8find_miniii2 = load i32, i32* %num1.addr, align 4
  call void @stg_update_load(i32* %num1.addr, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @19, i32 0, i32 0))
  %tmp__Z8find_miniii3 = load i32, i32* %num3.addr, align 4
  call void @stg_update_load(i32* %num3.addr, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @21, i32 0, i32 0))
  %cmp1 = icmp slt i32 %tmp__Z8find_miniii2, %tmp__Z8find_miniii3
  call void @stg_update_cmp(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @22, i32 0, i32 0), i8* getelementptr inbounds ([20 x i8], [20 x i8]* @23, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @25, i32 0, i32 0), i8* getelementptr inbounds ([20 x i8], [20 x i8]* @24, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @26, i32 0, i32 0))
  call void @stg_update_pc(i1 %cmp1, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @27, i32 0, i32 0))
  br i1 %cmp1, label %if.then2, label %if.else

if.then2:                                         ; preds = %if.then
  %tmp__Z8find_miniii4 = load i32, i32* %num1.addr, align 4
  call void @stg_update_load(i32* %num1.addr, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @30, i32 0, i32 0))
  store i32 %tmp__Z8find_miniii4, i32* %min, align 4
  call void @stg_update_store(i32* %min, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @31, i32 0, i32 0))
  br label %if.end

if.else:                                          ; preds = %if.then
  %tmp__Z8find_miniii5 = load i32, i32* %num3.addr, align 4
  call void @stg_update_load(i32* %num3.addr, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @34, i32 0, i32 0))
  store i32 %tmp__Z8find_miniii5, i32* %min, align 4
  call void @stg_update_store(i32* %min, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @35, i32 0, i32 0))
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then2
  br label %if.end8

if.else3:                                         ; preds = %entry
  %tmp__Z8find_miniii6 = load i32, i32* %num2.addr, align 4
  call void @stg_update_load(i32* %num2.addr, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @39, i32 0, i32 0))
  %tmp__Z8find_miniii7 = load i32, i32* %num3.addr, align 4
  call void @stg_update_load(i32* %num3.addr, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @41, i32 0, i32 0))
  %cmp4 = icmp slt i32 %tmp__Z8find_miniii6, %tmp__Z8find_miniii7
  call void @stg_update_cmp(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @42, i32 0, i32 0), i8* getelementptr inbounds ([20 x i8], [20 x i8]* @43, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @45, i32 0, i32 0), i8* getelementptr inbounds ([20 x i8], [20 x i8]* @44, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @46, i32 0, i32 0))
  call void @stg_update_pc(i1 %cmp4, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @47, i32 0, i32 0))
  br i1 %cmp4, label %if.then5, label %if.else6

if.then5:                                         ; preds = %if.else3
  %tmp__Z8find_miniii8 = load i32, i32* %num2.addr, align 4
  call void @stg_update_load(i32* %num2.addr, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @50, i32 0, i32 0))
  store i32 %tmp__Z8find_miniii8, i32* %min, align 4
  call void @stg_update_store(i32* %min, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @51, i32 0, i32 0))
  br label %if.end7

if.else6:                                         ; preds = %if.else3
  %tmp__Z8find_miniii9 = load i32, i32* %num3.addr, align 4
  call void @stg_update_load(i32* %num3.addr, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @54, i32 0, i32 0))
  store i32 %tmp__Z8find_miniii9, i32* %min, align 4
  call void @stg_update_store(i32* %min, i8* getelementptr inbounds ([20 x i8], [20 x i8]* @55, i32 0, i32 0))
  br label %if.end7

if.end7:                                          ; preds = %if.else6, %if.then5
  br label %if.end8

if.end8:                                          ; preds = %if.end7, %if.end
  %tmp__Z8find_miniii10 = load i32, i32* %num1.addr, align 4
  call void @stg_update_load(i32* %num1.addr, i8* getelementptr inbounds ([21 x i8], [21 x i8]* @59, i32 0, i32 0))
  %tmp__Z8find_miniii11 = load i32, i32* %num2.addr, align 4
  call void @stg_update_load(i32* %num2.addr, i8* getelementptr inbounds ([21 x i8], [21 x i8]* @61, i32 0, i32 0))
  %tmp__Z8find_miniii12 = load i32, i32* %num3.addr, align 4
  call void @stg_update_load(i32* %num3.addr, i8* getelementptr inbounds ([21 x i8], [21 x i8]* @63, i32 0, i32 0))
  %tmp__Z8find_miniii13 = load i32, i32* %min, align 4
  call void @stg_update_load(i32* %min, i8* getelementptr inbounds ([21 x i8], [21 x i8]* @65, i32 0, i32 0))
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.str, i32 0, i32 0), i32 %tmp__Z8find_miniii10, i32 %tmp__Z8find_miniii11, i32 %tmp__Z8find_miniii12, i32 %tmp__Z8find_miniii13)
  %tmp__Z8find_miniii14 = load i32, i32* %min, align 4
  call void @stg_update_load(i32* %min, i8* getelementptr inbounds ([21 x i8], [21 x i8]* @67, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([19 x i8], [19 x i8]* @68, i32 0, i32 0), i8* getelementptr inbounds ([21 x i8], [21 x i8]* @69, i32 0, i32 0))
  ret i32 %tmp__Z8find_miniii14
}

declare i32 @printf(i8*, ...) #1

; Function Attrs: noinline norecurse optnone ssp uwtable
define i32 @main() #2 {
entry:
  %retval = alloca i32, align 4
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %c = alloca i32, align 4
  store i32 0, i32* %retval, align 4
  call void @stg_update_store(i32* %retval, i8* getelementptr inbounds ([8 x i8], [8 x i8]* @75, i32 0, i32 0))
  call void @stg_begin_test()
  %tmp_main = bitcast i32* %a to i8*
  call void @stg_symbolic_variable(i8* %tmp_main, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.1, i32 0, i32 0))
  %tmp_main1 = bitcast i32* %b to i8*
  call void @stg_symbolic_variable(i8* %tmp_main1, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i32 0, i32 0))
  %tmp_main2 = bitcast i32* %c to i8*
  call void @stg_symbolic_variable(i8* %tmp_main2, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.3, i32 0, i32 0))
  %tmp_main3 = bitcast i32* %a to i8*
  call void @stg_input_int(i8* %tmp_main3, i32 38)
  %tmp_main4 = bitcast i32* %b to i8*
  call void @stg_input_int(i8* %tmp_main4, i32 78)
  %tmp_main5 = bitcast i32* %c to i8*
  call void @stg_input_int(i8* %tmp_main5, i32 78)
  %tmp_main6 = load i32, i32* %a, align 4
  call void @stg_update_load(i32* %a, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @83, i32 0, i32 0))
  %tmp_main7 = load i32, i32* %b, align 4
  call void @stg_update_load(i32* %b, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @85, i32 0, i32 0))
  %tmp_main8 = load i32, i32* %c, align 4
  call void @stg_update_load(i32* %c, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @87, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @88, i32 0, i32 0), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @89, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @90, i32 0, i32 0), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @91, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @92, i32 0, i32 0), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @93, i32 0, i32 0))
  %call = call i32 @_Z8find_miniii(i32 %tmp_main6, i32 %tmp_main7, i32 %tmp_main8)
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @94, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @95, i32 0, i32 0))
  call void @stg_assert(i1 zeroext true)
  call void @stg_end_test()
  call void @stg_begin_test()
  %tmp_main9 = bitcast i32* %a to i8*
  call void @stg_input_int(i8* %tmp_main9, i32 1)
  %tmp_main10 = bitcast i32* %b to i8*
  call void @stg_input_int(i8* %tmp_main10, i32 4)
  %tmp_main11 = bitcast i32* %c to i8*
  call void @stg_input_int(i8* %tmp_main11, i32 3)
  %tmp_main12 = load i32, i32* %a, align 4
  call void @stg_update_load(i32* %a, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @100, i32 0, i32 0))
  %tmp_main13 = load i32, i32* %b, align 4
  call void @stg_update_load(i32* %b, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @102, i32 0, i32 0))
  %tmp_main14 = load i32, i32* %c, align 4
  call void @stg_update_load(i32* %c, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @104, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @105, i32 0, i32 0), i8* getelementptr inbounds ([11 x i8], [11 x i8]* @106, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @107, i32 0, i32 0), i8* getelementptr inbounds ([11 x i8], [11 x i8]* @108, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @109, i32 0, i32 0), i8* getelementptr inbounds ([11 x i8], [11 x i8]* @110, i32 0, i32 0))
  %call1 = call i32 @_Z8find_miniii(i32 %tmp_main12, i32 %tmp_main13, i32 %tmp_main14)
  call void @stg_update_char(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @111, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @112, i32 0, i32 0))
  call void @stg_assert(i1 zeroext true)
  call void @stg_end_test()
  call void @stg_begin_test()
  %tmp_main15 = bitcast i32* %a to i8*
  call void @stg_input_int(i8* %tmp_main15, i32 1)
  %tmp_main16 = bitcast i32* %b to i8*
  call void @stg_input_int(i8* %tmp_main16, i32 1)
  %tmp_main17 = bitcast i32* %c to i8*
  call void @stg_input_int(i8* %tmp_main17, i32 1)
  %tmp_main18 = load i32, i32* %a, align 4
  call void @stg_update_load(i32* %a, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @117, i32 0, i32 0))
  %tmp_main19 = load i32, i32* %b, align 4
  call void @stg_update_load(i32* %b, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @119, i32 0, i32 0))
  %tmp_main20 = load i32, i32* %c, align 4
  call void @stg_update_load(i32* %c, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @121, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @122, i32 0, i32 0), i8* getelementptr inbounds ([11 x i8], [11 x i8]* @123, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @124, i32 0, i32 0), i8* getelementptr inbounds ([11 x i8], [11 x i8]* @125, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @126, i32 0, i32 0), i8* getelementptr inbounds ([11 x i8], [11 x i8]* @127, i32 0, i32 0))
  %call2 = call i32 @_Z8find_miniii(i32 %tmp_main18, i32 %tmp_main19, i32 %tmp_main20)
  call void @stg_update_char(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @128, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @129, i32 0, i32 0))
  call void @stg_assert(i1 zeroext true)
  call void @stg_end_test()
  call void @stg_update_char(i8* getelementptr inbounds ([9 x i8], [9 x i8]* @130, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @131, i32 0, i32 0))
  ret i32 0
}

declare void @stg_begin_test() #1

declare void @stg_symbolic_variable(i8*, i8*) #1

declare void @stg_input_int(i8*, i32) #1

declare void @stg_assert(i1 zeroext) #1

declare void @stg_end_test() #1

declare void @stg_update_op(i8*, i8*, i8*, i8*)

declare void @stg_update_cast(i8*, i8*, i8*, i8*)

declare void @stg_update_pc(i1, i8*)

declare void @stg_set_symbolic(i8*, i8*)

declare void @stg_update_char(i8*, i8*)

declare void @stg_update_phi(i8*, i8*, i8*)

declare void @stg_update_int(i8*, i32)

declare void @stg_update_load(i32*, i8*)

declare void @stg_update_store(i32*, i8*)

declare void @stg_update_load_i8(i8*, i8*)

declare void @stg_update_store_i8(i8*, i8*)

declare void @stg_update_load_float(float*, i8*)

declare void @stg_update_store_float(float*, i8*)

declare void @stg_update_cmp(i8*, i8*, i8*, i8*, i8*)

declare void @stg_update_load_i64(i64*, i8*)

declare void @stg_update_store_i64(i64*, i8*)

declare void @stg_update_store_double(double*, i8*)

declare void @stg_update_load_double(double*, i8*)

attributes #0 = { noinline optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noinline norecurse optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 10, i32 14]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"Apple LLVM version 10.0.1 (clang-1001.0.46.4)"}
