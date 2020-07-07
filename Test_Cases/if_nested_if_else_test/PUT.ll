; ModuleID = 'PUT.bc'
source_filename = "nested_if_else.cpp"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.14.0"

@.str = private unnamed_addr constant [2 x i8] c"X\00", align 1
@.str.1 = private unnamed_addr constant [2 x i8] c"Y\00", align 1
@.str.2 = private unnamed_addr constant [2 x i8] c"Z\00", align 1

; Function Attrs: noinline nounwind optnone ssp uwtable
define zeroext i1 @_Z10isMaxOrMiniii(i32 %a, i32 %b, i32 %c) #0 {
entry:
  %retval = alloca i1, align 1
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  %c.addr = alloca i32, align 4
  store i32 %a, i32* %a.addr, align 4
  store i32 %b, i32* %b.addr, align 4
  store i32 %c, i32* %c.addr, align 4
  %0 = load i32, i32* %a.addr, align 4
  %1 = load i32, i32* %b.addr, align 4
  %cmp = icmp sgt i32 %0, %1
  br i1 %cmp, label %if.then, label %if.else3

if.then:                                          ; preds = %entry
  %2 = load i32, i32* %a.addr, align 4
  %3 = load i32, i32* %c.addr, align 4
  %cmp1 = icmp sgt i32 %2, %3
  br i1 %cmp1, label %if.then2, label %if.else

if.then2:                                         ; preds = %if.then
  store i1 true, i1* %retval, align 1
  br label %return

if.else:                                          ; preds = %if.then
  store i1 false, i1* %retval, align 1
  br label %return

if.else3:                                         ; preds = %entry
  %4 = load i32, i32* %b.addr, align 4
  %5 = load i32, i32* %c.addr, align 4
  %cmp4 = icmp sgt i32 %4, %5
  br i1 %cmp4, label %if.then5, label %if.else6

if.then5:                                         ; preds = %if.else3
  store i1 true, i1* %retval, align 1
  br label %return

if.else6:                                         ; preds = %if.else3
  store i1 false, i1* %retval, align 1
  br label %return

return:                                           ; preds = %if.else6, %if.then5, %if.else, %if.then2
  %6 = load i1, i1* %retval, align 1
  ret i1 %6
}

; Function Attrs: noinline norecurse optnone ssp uwtable
define i32 @main() #1 {
entry:
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %c = alloca i32, align 4
  call void @stg_begin_test()
  %0 = bitcast i32* %a to i8*
  call void @stg_symbolic_variable(i8* %0, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i32 0, i32 0))
  %1 = bitcast i32* %b to i8*
  call void @stg_symbolic_variable(i8* %1, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.1, i32 0, i32 0))
  %2 = bitcast i32* %c to i8*
  call void @stg_symbolic_variable(i8* %2, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i32 0, i32 0))
  %3 = bitcast i32* %a to i8*
  call void @stg_input_int(i8* %3, i32 550)
  %4 = bitcast i32* %b to i8*
  call void @stg_input_int(i8* %4, i32 38)
  %5 = bitcast i32* %c to i8*
  call void @stg_input_int(i8* %5, i32 58)
  %6 = load i32, i32* %a, align 4
  %7 = load i32, i32* %b, align 4
  %8 = load i32, i32* %c, align 4
  %call = call zeroext i1 @_Z10isMaxOrMiniii(i32 %6, i32 %7, i32 %8)
  call void @stg_assert(i1 zeroext %call)
  call void @stg_end_test()
  call void @stg_begin_test()
  %9 = bitcast i32* %a to i8*
  call void @stg_input_int(i8* %9, i32 0)
  %10 = bitcast i32* %b to i8*
  call void @stg_input_int(i8* %10, i32 38)
  %11 = bitcast i32* %c to i8*
  call void @stg_input_int(i8* %11, i32 58)
  %12 = load i32, i32* %a, align 4
  %13 = load i32, i32* %b, align 4
  %14 = load i32, i32* %c, align 4
  %call1 = call zeroext i1 @_Z10isMaxOrMiniii(i32 %12, i32 %13, i32 %14)
  call void @stg_assert(i1 zeroext %call1)
  call void @stg_end_test()
  call void @stg_begin_test()
  %15 = bitcast i32* %a to i8*
  call void @stg_input_int(i8* %15, i32 5)
  %16 = bitcast i32* %b to i8*
  call void @stg_input_int(i8* %16, i32 38)
  %17 = bitcast i32* %c to i8*
  call void @stg_input_int(i8* %17, i32 58)
  %18 = load i32, i32* %a, align 4
  %19 = load i32, i32* %b, align 4
  %20 = load i32, i32* %c, align 4
  %call2 = call zeroext i1 @_Z10isMaxOrMiniii(i32 %18, i32 %19, i32 %20)
  call void @stg_assert(i1 zeroext %call2)
  call void @stg_end_test()
  ret i32 0
}

declare void @stg_begin_test() #2

declare void @stg_symbolic_variable(i8*, i8*) #2

declare void @stg_input_int(i8*, i32) #2

declare void @stg_assert(i1 zeroext) #2

declare void @stg_end_test() #2

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noinline norecurse optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 10, i32 14]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"Apple LLVM version 10.0.1 (clang-1001.0.46.4)"}
