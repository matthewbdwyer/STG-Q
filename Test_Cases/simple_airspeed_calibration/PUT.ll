; ModuleID = 'PUT.bc'
source_filename = "simple_airspeed_calibration.cpp"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.14.0"

@readAir = global [5 x float] zeroinitializer, align 16
@.str = private unnamed_addr constant [24 x i8] c"calibration_counter %d\0A\00", align 1
@.str.1 = private unnamed_addr constant [16 x i8] c"retun value %d\0A\00", align 1
@__const.main.valueArray = private unnamed_addr constant [5 x float] [float 0x40344CCCC0000000, float 4.500000e+00, float 0x4021666660000000, float 8.000000e+00, float 0x4020666660000000], align 16
@__const.main.valueArray1 = private unnamed_addr constant [5 x float] [float 0x40344CCCC0000000, float 4.500000e+00, float 0x40495999A0000000, float 8.000000e+00, float 0x4020666660000000], align 16
@.str.2 = private unnamed_addr constant [6 x i8] c"float\00", align 1
@.str.3 = private unnamed_addr constant [2 x i8] c"S\00", align 1

; Function Attrs: noinline optnone ssp uwtable
define zeroext i1 @_Z23do_airspeed_calibrationf(float %analog_scaling) #0 {
entry:
  %analog_scaling.addr = alloca float, align 4
  %successfulCalibration = alloca i32, align 4
  %calibration_counter = alloca i32, align 4
  %calibration_count = alloca i32, align 4
  %diff_pres_filtered_pa = alloca float, align 4
  store float %analog_scaling, float* %analog_scaling.addr, align 4
  store i32 0, i32* %successfulCalibration, align 4
  store i32 0, i32* %calibration_counter, align 4
  store i32 3, i32* %calibration_count, align 4
  %0 = load float, float* %analog_scaling.addr, align 4
  %conv = fpext float %0 to double
  %cmp = fcmp olt double %conv, 1.000000e-01
  br i1 %cmp, label %land.lhs.true, label %if.else

land.lhs.true:                                    ; preds = %entry
  %1 = load float, float* %analog_scaling.addr, align 4
  %conv1 = fpext float %1 to double
  %cmp2 = fcmp ogt double %conv1, -1.000000e-01
  br i1 %cmp2, label %if.then, label %if.else

if.then:                                          ; preds = %land.lhs.true
  store i32 0, i32* %successfulCalibration, align 4
  br label %if.end9

if.else:                                          ; preds = %land.lhs.true, %entry
  br label %while.cond

while.cond:                                       ; preds = %if.end8, %if.else
  %2 = load i32, i32* %calibration_counter, align 4
  %cmp3 = icmp slt i32 %2, 5
  br i1 %cmp3, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %3 = load i32, i32* %calibration_counter, align 4
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([24 x i8], [24 x i8]* @.str, i32 0, i32 0), i32 %3)
  %4 = load i32, i32* %calibration_counter, align 4
  %idxprom = sext i32 %4 to i64
  %arrayidx = getelementptr inbounds [5 x float], [5 x float]* @readAir, i64 0, i64 %idxprom
  %5 = load float, float* %arrayidx, align 4
  store float %5, float* %diff_pres_filtered_pa, align 4
  %6 = load float, float* %diff_pres_filtered_pa, align 4
  %cmp4 = fcmp ogt float %6, 5.000000e+01
  br i1 %cmp4, label %if.then5, label %if.end

if.then5:                                         ; preds = %while.body
  store i32 1, i32* %successfulCalibration, align 4
  br label %while.end

if.end:                                           ; preds = %while.body
  %7 = load float, float* %diff_pres_filtered_pa, align 4
  %cmp6 = fcmp olt float %7, 0.000000e+00
  br i1 %cmp6, label %if.then7, label %if.end8

if.then7:                                         ; preds = %if.end
  store i32 0, i32* %successfulCalibration, align 4
  br label %while.end

if.end8:                                          ; preds = %if.end
  %8 = load i32, i32* %calibration_counter, align 4
  %inc = add nsw i32 %8, 1
  store i32 %inc, i32* %calibration_counter, align 4
  br label %while.cond

while.end:                                        ; preds = %if.then7, %if.then5, %while.cond
  br label %if.end9

if.end9:                                          ; preds = %while.end, %if.then
  %9 = load i32, i32* %calibration_counter, align 4
  %cmp10 = icmp eq i32 %9, 5
  br i1 %cmp10, label %if.then11, label %if.end12

if.then11:                                        ; preds = %if.end9
  store i32 0, i32* %successfulCalibration, align 4
  br label %if.end12

if.end12:                                         ; preds = %if.then11, %if.end9
  %10 = load i32, i32* %successfulCalibration, align 4
  %call13 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.1, i32 0, i32 0), i32 %10)
  %11 = load i32, i32* %successfulCalibration, align 4
  %tobool = icmp ne i32 %11, 0
  ret i1 %tobool
}

declare i32 @printf(i8*, ...) #1

; Function Attrs: noinline norecurse optnone ssp uwtable
define i32 @main() #2 {
entry:
  %valueArray = alloca [5 x float], align 16
  %valueArray1 = alloca [5 x float], align 16
  %0 = bitcast [5 x float]* %valueArray to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 16 %0, i8* align 16 bitcast ([5 x float]* @__const.main.valueArray to i8*), i64 20, i1 false)
  %1 = bitcast [5 x float]* %valueArray1 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 16 %1, i8* align 16 bitcast ([5 x float]* @__const.main.valueArray1 to i8*), i64 20, i1 false)
  call void @stg_begin_test()
  call void @stg_symbolic_array(i8* bitcast ([5 x float]* @readAir to i8*), i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.2, i32 0, i32 0), i32 5, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.3, i32 0, i32 0))
  %arraydecay = getelementptr inbounds [5 x float], [5 x float]* %valueArray, i32 0, i32 0
  %2 = bitcast float* %arraydecay to i8*
  call void @stg_input_array(i8* bitcast ([5 x float]* @readAir to i8*), i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.2, i32 0, i32 0), i32 5, i8* %2)
  %call = call zeroext i1 @_Z23do_airspeed_calibrationf(float 1.000000e+00)
  call void @stg_assert(i1 zeroext %call)
  call void @stg_end_test()
  call void @stg_begin_test()
  call void @stg_symbolic_array(i8* bitcast ([5 x float]* @readAir to i8*), i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.2, i32 0, i32 0), i32 5, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.3, i32 0, i32 0))
  %arraydecay1 = getelementptr inbounds [5 x float], [5 x float]* %valueArray1, i32 0, i32 0
  %3 = bitcast float* %arraydecay1 to i8*
  call void @stg_input_array(i8* bitcast ([5 x float]* @readAir to i8*), i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.2, i32 0, i32 0), i32 5, i8* %3)
  %call2 = call zeroext i1 @_Z23do_airspeed_calibrationf(float 1.000000e+00)
  call void @stg_assert(i1 zeroext %call2)
  call void @stg_end_test()
  ret i32 0
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #3

declare void @stg_begin_test() #1

declare void @stg_symbolic_array(i8*, i8*, i32, i8*) #1

declare void @stg_input_array(i8*, i8*, i32, i8*) #1

declare void @stg_assert(i1 zeroext) #1

declare void @stg_end_test() #1

attributes #0 = { noinline optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noinline norecurse optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { argmemonly nounwind willreturn }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 10, i32 14]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"Apple LLVM version 10.0.1 (clang-1001.0.46.4)"}
