; ModuleID = 'IPUT.bc'
source_filename = "complex_if.cpp"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.14.0"

@.str = private unnamed_addr constant [2 x i8] c"A\00", align 1
@.str.1 = private unnamed_addr constant [2 x i8] c"B\00", align 1
@prev_bb = global i8* getelementptr inbounds ([6 x i8], [6 x i8]* @65, i32 0, i32 0), align 4
@0 = private unnamed_addr constant [7 x i8] c"retval\00", align 1
@1 = private unnamed_addr constant [7 x i8] c"a.addr\00", align 1
@2 = private unnamed_addr constant [7 x i8] c"b.addr\00", align 1
@3 = private unnamed_addr constant [2 x i8] c"c\00", align 1
@4 = private unnamed_addr constant [2 x i8] c"d\00", align 1
@5 = private unnamed_addr constant [2 x i8] c"a\00", align 1
@6 = private unnamed_addr constant [2 x i8] c"b\00", align 1
@7 = private unnamed_addr constant [18 x i8] c"tmp__Z8find_maxii\00", align 1
@8 = private unnamed_addr constant [18 x i8] c"tmp__Z8find_maxii\00", align 1
@9 = private unnamed_addr constant [4 x i8] c"add\00", align 1
@10 = private unnamed_addr constant [9 x i8] c"(i32 10)\00", align 1
@11 = private unnamed_addr constant [4 x i8] c"add\00", align 1
@12 = private unnamed_addr constant [18 x i8] c"tmp__Z8find_maxii\00", align 1
@13 = private unnamed_addr constant [4 x i8] c"add\00", align 1
@14 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii1\00", align 1
@15 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii1\00", align 1
@16 = private unnamed_addr constant [4 x i8] c"sub\00", align 1
@17 = private unnamed_addr constant [9 x i8] c"(i32 10)\00", align 1
@18 = private unnamed_addr constant [4 x i8] c"sub\00", align 1
@19 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii1\00", align 1
@20 = private unnamed_addr constant [4 x i8] c"sub\00", align 1
@21 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii2\00", align 1
@22 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii2\00", align 1
@23 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii3\00", align 1
@24 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii3\00", align 1
@25 = private unnamed_addr constant [4 x i8] c"cmp\00", align 1
@26 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii2\00", align 1
@27 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii3\00", align 1
@28 = private unnamed_addr constant [4 x i8] c"sgt\00", align 1
@29 = private unnamed_addr constant [4 x i8] c"i32\00", align 1
@30 = private unnamed_addr constant [4 x i8] c"cmp\00", align 1
@31 = private unnamed_addr constant [6 x i8] c"entry\00", align 1
@32 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii4\00", align 1
@33 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii4\00", align 1
@34 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii4\00", align 1
@35 = private unnamed_addr constant [8 x i8] c"if.then\00", align 1
@36 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii5\00", align 1
@37 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii5\00", align 1
@38 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii5\00", align 1
@39 = private unnamed_addr constant [8 x i8] c"if.else\00", align 1
@40 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii6\00", align 1
@41 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii6\00", align 1
@42 = private unnamed_addr constant [18 x i8] c"_Z8find_maxii_RET\00", align 1
@43 = private unnamed_addr constant [19 x i8] c"tmp__Z8find_maxii6\00", align 1
@44 = private unnamed_addr constant [7 x i8] c"return\00", align 1
@45 = private unnamed_addr constant [7 x i8] c"retval\00", align 1
@46 = private unnamed_addr constant [2 x i8] c"a\00", align 1
@47 = private unnamed_addr constant [2 x i8] c"b\00", align 1
@48 = private unnamed_addr constant [8 x i8] c"(i32 0)\00", align 1
@49 = private unnamed_addr constant [9 x i8] c"tmp_main\00", align 1
@50 = private unnamed_addr constant [10 x i8] c"tmp_main1\00", align 1
@51 = private unnamed_addr constant [10 x i8] c"tmp_main2\00", align 1
@52 = private unnamed_addr constant [10 x i8] c"tmp_main3\00", align 1
@53 = private unnamed_addr constant [10 x i8] c"tmp_main4\00", align 1
@54 = private unnamed_addr constant [10 x i8] c"tmp_main4\00", align 1
@55 = private unnamed_addr constant [10 x i8] c"tmp_main5\00", align 1
@56 = private unnamed_addr constant [10 x i8] c"tmp_main5\00", align 1
@57 = private unnamed_addr constant [2 x i8] c"a\00", align 1
@58 = private unnamed_addr constant [10 x i8] c"tmp_main4\00", align 1
@59 = private unnamed_addr constant [2 x i8] c"b\00", align 1
@60 = private unnamed_addr constant [10 x i8] c"tmp_main5\00", align 1
@61 = private unnamed_addr constant [5 x i8] c"call\00", align 1
@62 = private unnamed_addr constant [18 x i8] c"_Z8find_maxii_RET\00", align 1
@63 = private unnamed_addr constant [9 x i8] c"main_RET\00", align 1
@64 = private unnamed_addr constant [2 x i8] c"0\00", align 1
@65 = private unnamed_addr constant [6 x i8] c"entry\00", align 1

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @_Z8find_maxii(i32 %a, i32 %b) #0 {
entry:
  %retval = alloca i32, align 4
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  %c = alloca i32, align 4
  %d = alloca i32, align 4
  store i32 %a, i32* %a.addr, align 4
  call void @stg_update_store(i32* %a.addr, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @5, i32 0, i32 0))
  store i32 %b, i32* %b.addr, align 4
  call void @stg_update_store(i32* %b.addr, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @6, i32 0, i32 0))
  %tmp__Z8find_maxii = load i32, i32* %a.addr, align 4
  call void @stg_update_load(i32* %a.addr, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @8, i32 0, i32 0))
  %add = add nsw i32 10, %tmp__Z8find_maxii
  call void @stg_update_op(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @9, i32 0, i32 0), i8* getelementptr inbounds ([9 x i8], [9 x i8]* @10, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @11, i32 0, i32 0), i8* getelementptr inbounds ([18 x i8], [18 x i8]* @12, i32 0, i32 0))
  store i32 %add, i32* %c, align 4
  call void @stg_update_store(i32* %c, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @13, i32 0, i32 0))
  %tmp__Z8find_maxii1 = load i32, i32* %b.addr, align 4
  call void @stg_update_load(i32* %b.addr, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @15, i32 0, i32 0))
  %sub = sub nsw i32 10, %tmp__Z8find_maxii1
  call void @stg_update_op(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @16, i32 0, i32 0), i8* getelementptr inbounds ([9 x i8], [9 x i8]* @17, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @18, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @19, i32 0, i32 0))
  store i32 %sub, i32* %d, align 4
  call void @stg_update_store(i32* %d, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @20, i32 0, i32 0))
  %tmp__Z8find_maxii2 = load i32, i32* %c, align 4
  call void @stg_update_load(i32* %c, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @22, i32 0, i32 0))
  %tmp__Z8find_maxii3 = load i32, i32* %d, align 4
  call void @stg_update_load(i32* %d, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @24, i32 0, i32 0))
  %cmp = icmp sgt i32 %tmp__Z8find_maxii2, %tmp__Z8find_maxii3
  call void @stg_update_cmp(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @25, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @26, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @28, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @27, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @29, i32 0, i32 0))
  call void @stg_update_pc(i1 %cmp, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @30, i32 0, i32 0))
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %tmp__Z8find_maxii4 = load i32, i32* %a.addr, align 4
  call void @stg_update_load(i32* %a.addr, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @33, i32 0, i32 0))
  store i32 %tmp__Z8find_maxii4, i32* %retval, align 4
  call void @stg_update_store(i32* %retval, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @34, i32 0, i32 0))
  br label %return

if.else:                                          ; preds = %entry
  %tmp__Z8find_maxii5 = load i32, i32* %b.addr, align 4
  call void @stg_update_load(i32* %b.addr, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @37, i32 0, i32 0))
  store i32 %tmp__Z8find_maxii5, i32* %retval, align 4
  call void @stg_update_store(i32* %retval, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @38, i32 0, i32 0))
  br label %return

return:                                           ; preds = %if.else, %if.then
  %tmp__Z8find_maxii6 = load i32, i32* %retval, align 4
  call void @stg_update_load(i32* %retval, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @41, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @42, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @43, i32 0, i32 0))
  ret i32 %tmp__Z8find_maxii6
}

; Function Attrs: noinline norecurse optnone ssp uwtable
define i32 @main() #1 {
entry:
  %retval = alloca i32, align 4
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  store i32 0, i32* %retval, align 4
  call void @stg_update_store(i32* %retval, i8* getelementptr inbounds ([8 x i8], [8 x i8]* @48, i32 0, i32 0))
  call void @stg_begin_test()
  %tmp_main = bitcast i32* %a to i8*
  call void @stg_symbolic_variable(i8* %tmp_main, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i32 0, i32 0))
  %tmp_main1 = bitcast i32* %b to i8*
  call void @stg_symbolic_variable(i8* %tmp_main1, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.1, i32 0, i32 0))
  %tmp_main2 = bitcast i32* %a to i8*
  call void @stg_input_int(i8* %tmp_main2, i32 38)
  %tmp_main3 = bitcast i32* %b to i8*
  call void @stg_input_int(i8* %tmp_main3, i32 78)
  %tmp_main4 = load i32, i32* %a, align 4
  call void @stg_update_load(i32* %a, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @54, i32 0, i32 0))
  %tmp_main5 = load i32, i32* %b, align 4
  call void @stg_update_load(i32* %b, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @56, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @57, i32 0, i32 0), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @58, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @59, i32 0, i32 0), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @60, i32 0, i32 0))
  %call = call i32 @_Z8find_maxii(i32 %tmp_main4, i32 %tmp_main5)
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @61, i32 0, i32 0), i8* getelementptr inbounds ([18 x i8], [18 x i8]* @62, i32 0, i32 0))
  call void @stg_assert(i1 zeroext true)
  call void @stg_end_test()
  call void @stg_update_char(i8* getelementptr inbounds ([9 x i8], [9 x i8]* @63, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @64, i32 0, i32 0))
  ret i32 0
}

declare void @stg_begin_test() #2

declare void @stg_symbolic_variable(i8*, i8*) #2

declare void @stg_input_int(i8*, i32) #2

declare void @stg_assert(i1 zeroext) #2

declare void @stg_end_test() #2

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

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noinline norecurse optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 10, i32 14]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"Apple LLVM version 10.0.1 (clang-1001.0.46.4)"}
