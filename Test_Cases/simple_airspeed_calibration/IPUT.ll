; ModuleID = 'IPUT.bc'
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
@prev_bb = global i8* getelementptr inbounds ([6 x i8], [6 x i8]* @127, i32 0, i32 0), align 4
@0 = private unnamed_addr constant [22 x i8] c"successfulCalibration\00", align 1
@1 = private unnamed_addr constant [20 x i8] c"calibration_counter\00", align 1
@2 = private unnamed_addr constant [18 x i8] c"calibration_count\00", align 1
@3 = private unnamed_addr constant [23 x i8] c"v(analog_scaling.addr)\00", align 1
@4 = private unnamed_addr constant [15 x i8] c"analog_scaling\00", align 1
@5 = private unnamed_addr constant [25 x i8] c"v(successfulCalibration)\00", align 1
@6 = private unnamed_addr constant [2 x i8] c"0\00", align 1
@7 = private unnamed_addr constant [23 x i8] c"v(calibration_counter)\00", align 1
@8 = private unnamed_addr constant [2 x i8] c"0\00", align 1
@9 = private unnamed_addr constant [21 x i8] c"v(calibration_count)\00", align 1
@10 = private unnamed_addr constant [2 x i8] c"3\00", align 1
@11 = private unnamed_addr constant [33 x i8] c"tmp__Z23do_airspeed_calibrationf\00", align 1
@12 = private unnamed_addr constant [33 x i8] c"tmp__Z23do_airspeed_calibrationf\00", align 1
@13 = private unnamed_addr constant [5 x i8] c"conv\00", align 1
@14 = private unnamed_addr constant [33 x i8] c"tmp__Z23do_airspeed_calibrationf\00", align 1
@15 = private unnamed_addr constant [4 x i8] c"cmp\00", align 1
@16 = private unnamed_addr constant [5 x i8] c"conv\00", align 1
@17 = private unnamed_addr constant [2 x i8] c"<\00", align 1
@18 = private unnamed_addr constant [9 x i8] c"0.100000\00", align 1
@19 = private unnamed_addr constant [4 x i8] c"cmp\00", align 1
@20 = private unnamed_addr constant [6 x i8] c"entry\00", align 1
@21 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf1\00", align 1
@22 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf1\00", align 1
@23 = private unnamed_addr constant [6 x i8] c"conv1\00", align 1
@24 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf1\00", align 1
@25 = private unnamed_addr constant [5 x i8] c"cmp2\00", align 1
@26 = private unnamed_addr constant [6 x i8] c"conv1\00", align 1
@27 = private unnamed_addr constant [2 x i8] c">\00", align 1
@28 = private unnamed_addr constant [10 x i8] c"-0.100000\00", align 1
@29 = private unnamed_addr constant [5 x i8] c"cmp2\00", align 1
@30 = private unnamed_addr constant [14 x i8] c"land.lhs.true\00", align 1
@31 = private unnamed_addr constant [25 x i8] c"v(successfulCalibration)\00", align 1
@32 = private unnamed_addr constant [2 x i8] c"0\00", align 1
@33 = private unnamed_addr constant [8 x i8] c"if.then\00", align 1
@34 = private unnamed_addr constant [8 x i8] c"if.else\00", align 1
@35 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf2\00", align 1
@36 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf2\00", align 1
@37 = private unnamed_addr constant [5 x i8] c"cmp3\00", align 1
@38 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf2\00", align 1
@39 = private unnamed_addr constant [2 x i8] c"<\00", align 1
@40 = private unnamed_addr constant [2 x i8] c"5\00", align 1
@41 = private unnamed_addr constant [5 x i8] c"cmp3\00", align 1
@42 = private unnamed_addr constant [11 x i8] c"while.cond\00", align 1
@43 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf3\00", align 1
@44 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf3\00", align 1
@45 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf4\00", align 1
@46 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf4\00", align 1
@47 = private unnamed_addr constant [11 x i8] c"idxprom = \00", align 1
@48 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf4\00", align 1
@49 = private unnamed_addr constant [12 x i8] c"arrayidx = \00", align 1
@50 = private unnamed_addr constant [17 x i8] c"readAir[idxprom]\00", align 1
@51 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf5\00", align 1
@52 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf5\00", align 1
@53 = private unnamed_addr constant [25 x i8] c"v(diff_pres_filtered_pa)\00", align 1
@54 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf5\00", align 1
@55 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf6\00", align 1
@56 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf6\00", align 1
@57 = private unnamed_addr constant [5 x i8] c"cmp4\00", align 1
@58 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf6\00", align 1
@59 = private unnamed_addr constant [2 x i8] c">\00", align 1
@60 = private unnamed_addr constant [10 x i8] c"50.000000\00", align 1
@61 = private unnamed_addr constant [5 x i8] c"cmp4\00", align 1
@62 = private unnamed_addr constant [11 x i8] c"while.body\00", align 1
@63 = private unnamed_addr constant [25 x i8] c"v(successfulCalibration)\00", align 1
@64 = private unnamed_addr constant [2 x i8] c"1\00", align 1
@65 = private unnamed_addr constant [9 x i8] c"if.then5\00", align 1
@66 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf7\00", align 1
@67 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf7\00", align 1
@68 = private unnamed_addr constant [5 x i8] c"cmp6\00", align 1
@69 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf7\00", align 1
@70 = private unnamed_addr constant [2 x i8] c"<\00", align 1
@71 = private unnamed_addr constant [9 x i8] c"0.000000\00", align 1
@72 = private unnamed_addr constant [5 x i8] c"cmp6\00", align 1
@73 = private unnamed_addr constant [7 x i8] c"if.end\00", align 1
@74 = private unnamed_addr constant [25 x i8] c"v(successfulCalibration)\00", align 1
@75 = private unnamed_addr constant [2 x i8] c"0\00", align 1
@76 = private unnamed_addr constant [9 x i8] c"if.then7\00", align 1
@77 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf8\00", align 1
@78 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf8\00", align 1
@79 = private unnamed_addr constant [4 x i8] c"inc\00", align 1
@80 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf8\00", align 1
@81 = private unnamed_addr constant [4 x i8] c" + \00", align 1
@82 = private unnamed_addr constant [2 x i8] c"1\00", align 1
@83 = private unnamed_addr constant [23 x i8] c"v(calibration_counter)\00", align 1
@84 = private unnamed_addr constant [4 x i8] c"inc\00", align 1
@85 = private unnamed_addr constant [8 x i8] c"if.end8\00", align 1
@86 = private unnamed_addr constant [10 x i8] c"while.end\00", align 1
@87 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf9\00", align 1
@88 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf9\00", align 1
@89 = private unnamed_addr constant [6 x i8] c"cmp10\00", align 1
@90 = private unnamed_addr constant [34 x i8] c"tmp__Z23do_airspeed_calibrationf9\00", align 1
@91 = private unnamed_addr constant [3 x i8] c"==\00", align 1
@92 = private unnamed_addr constant [2 x i8] c"5\00", align 1
@93 = private unnamed_addr constant [6 x i8] c"cmp10\00", align 1
@94 = private unnamed_addr constant [8 x i8] c"if.end9\00", align 1
@95 = private unnamed_addr constant [25 x i8] c"v(successfulCalibration)\00", align 1
@96 = private unnamed_addr constant [2 x i8] c"0\00", align 1
@97 = private unnamed_addr constant [10 x i8] c"if.then11\00", align 1
@98 = private unnamed_addr constant [35 x i8] c"tmp__Z23do_airspeed_calibrationf10\00", align 1
@99 = private unnamed_addr constant [35 x i8] c"tmp__Z23do_airspeed_calibrationf10\00", align 1
@100 = private unnamed_addr constant [35 x i8] c"tmp__Z23do_airspeed_calibrationf11\00", align 1
@101 = private unnamed_addr constant [35 x i8] c"tmp__Z23do_airspeed_calibrationf11\00", align 1
@102 = private unnamed_addr constant [7 x i8] c"tobool\00", align 1
@103 = private unnamed_addr constant [35 x i8] c"tmp__Z23do_airspeed_calibrationf11\00", align 1
@104 = private unnamed_addr constant [3 x i8] c"!=\00", align 1
@105 = private unnamed_addr constant [2 x i8] c"0\00", align 1
@106 = private unnamed_addr constant [33 x i8] c"_Z23do_airspeed_calibrationf_RET\00", align 1
@107 = private unnamed_addr constant [7 x i8] c"tobool\00", align 1
@108 = private unnamed_addr constant [9 x i8] c"if.end12\00", align 1
@109 = private unnamed_addr constant [5 x i8] c"v(&)\00", align 1
@110 = private unnamed_addr constant [11 x i8] c"valueArray\00", align 1
@111 = private unnamed_addr constant [5 x i8] c"v(&)\00", align 1
@112 = private unnamed_addr constant [12 x i8] c"valueArray1\00", align 1
@113 = private unnamed_addr constant [14 x i8] c"arraydecay = \00", align 1
@114 = private unnamed_addr constant [14 x i8] c"valueArray[0]\00", align 1
@115 = private unnamed_addr constant [15 x i8] c"analog_scaling\00", align 1
@116 = private unnamed_addr constant [9 x i8] c"1.000000\00", align 1
@117 = private unnamed_addr constant [5 x i8] c"call\00", align 1
@118 = private unnamed_addr constant [33 x i8] c"_Z23do_airspeed_calibrationf_RET\00", align 1
@119 = private unnamed_addr constant [15 x i8] c"arraydecay1 = \00", align 1
@120 = private unnamed_addr constant [15 x i8] c"valueArray1[0]\00", align 1
@121 = private unnamed_addr constant [15 x i8] c"analog_scaling\00", align 1
@122 = private unnamed_addr constant [9 x i8] c"1.000000\00", align 1
@123 = private unnamed_addr constant [6 x i8] c"call2\00", align 1
@124 = private unnamed_addr constant [33 x i8] c"_Z23do_airspeed_calibrationf_RET\00", align 1
@125 = private unnamed_addr constant [9 x i8] c"main_RET\00", align 1
@126 = private unnamed_addr constant [2 x i8] c"0\00", align 1
@127 = private unnamed_addr constant [6 x i8] c"entry\00", align 1

; Function Attrs: noinline optnone ssp uwtable
define zeroext i1 @_Z23do_airspeed_calibrationf(float %analog_scaling) #0 {
entry:
  %analog_scaling.addr = alloca float, align 4
  %successfulCalibration = alloca i32, align 4
  %calibration_counter = alloca i32, align 4
  %calibration_count = alloca i32, align 4
  %diff_pres_filtered_pa = alloca float, align 4
  store float %analog_scaling, float* %analog_scaling.addr, align 4
  call void @stg_update_store_float(float* %analog_scaling.addr, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @4, i32 0, i32 0))
  store i32 0, i32* %successfulCalibration, align 4
  call void @stg_update_store(i32* %successfulCalibration, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @6, i32 0, i32 0))
  store i32 0, i32* %calibration_counter, align 4
  call void @stg_update_store(i32* %calibration_counter, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @8, i32 0, i32 0))
  store i32 3, i32* %calibration_count, align 4
  call void @stg_update_store(i32* %calibration_count, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @10, i32 0, i32 0))
  %tmp__Z23do_airspeed_calibrationf = load float, float* %analog_scaling.addr, align 4
  call void @stg_update_load_float(float* %analog_scaling.addr, i8* getelementptr inbounds ([33 x i8], [33 x i8]* @12, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @13, i32 0, i32 0), i8* getelementptr inbounds ([33 x i8], [33 x i8]* @14, i32 0, i32 0))
  %conv = fpext float %tmp__Z23do_airspeed_calibrationf to double
  %cmp = fcmp olt double %conv, 1.000000e-01
  call void @stg_update_op(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @15, i32 0, i32 0), i8* getelementptr inbounds ([5 x i8], [5 x i8]* @16, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @17, i32 0, i32 0), i8* getelementptr inbounds ([9 x i8], [9 x i8]* @18, i32 0, i32 0))
  call void @stg_update_pc(i1 %cmp, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @19, i32 0, i32 0))
  br i1 %cmp, label %land.lhs.true, label %if.else

land.lhs.true:                                    ; preds = %entry
  %tmp__Z23do_airspeed_calibrationf1 = load float, float* %analog_scaling.addr, align 4
  call void @stg_update_load_float(float* %analog_scaling.addr, i8* getelementptr inbounds ([34 x i8], [34 x i8]* @22, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @23, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8], [34 x i8]* @24, i32 0, i32 0))
  %conv1 = fpext float %tmp__Z23do_airspeed_calibrationf1 to double
  %cmp2 = fcmp ogt double %conv1, -1.000000e-01
  call void @stg_update_op(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @25, i32 0, i32 0), i8* getelementptr inbounds ([6 x i8], [6 x i8]* @26, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @27, i32 0, i32 0), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @28, i32 0, i32 0))
  call void @stg_update_pc(i1 %cmp2, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @29, i32 0, i32 0))
  br i1 %cmp2, label %if.then, label %if.else

if.then:                                          ; preds = %land.lhs.true
  store i32 0, i32* %successfulCalibration, align 4
  call void @stg_update_store(i32* %successfulCalibration, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @32, i32 0, i32 0))
  br label %if.end9

if.else:                                          ; preds = %land.lhs.true, %entry
  br label %while.cond

while.cond:                                       ; preds = %if.end8, %if.else
  %tmp__Z23do_airspeed_calibrationf2 = load i32, i32* %calibration_counter, align 4
  call void @stg_update_load(i32* %calibration_counter, i8* getelementptr inbounds ([34 x i8], [34 x i8]* @36, i32 0, i32 0))
  %cmp3 = icmp slt i32 %tmp__Z23do_airspeed_calibrationf2, 5
  call void @stg_update_op(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @37, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8], [34 x i8]* @38, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @39, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @40, i32 0, i32 0))
  call void @stg_update_pc(i1 %cmp3, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @41, i32 0, i32 0))
  br i1 %cmp3, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %tmp__Z23do_airspeed_calibrationf3 = load i32, i32* %calibration_counter, align 4
  call void @stg_update_load(i32* %calibration_counter, i8* getelementptr inbounds ([34 x i8], [34 x i8]* @44, i32 0, i32 0))
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([24 x i8], [24 x i8]* @.str, i32 0, i32 0), i32 %tmp__Z23do_airspeed_calibrationf3)
  %tmp__Z23do_airspeed_calibrationf4 = load i32, i32* %calibration_counter, align 4
  call void @stg_update_load(i32* %calibration_counter, i8* getelementptr inbounds ([34 x i8], [34 x i8]* @46, i32 0, i32 0))
  %idxprom = sext i32 %tmp__Z23do_airspeed_calibrationf4 to i64
  %arrayidx = getelementptr inbounds [5 x float], [5 x float]* @readAir, i64 0, i64 %idxprom
  %tmp__Z23do_airspeed_calibrationf5 = load float, float* %arrayidx, align 4
  call void @stg_update_load_float(float* %arrayidx, i8* getelementptr inbounds ([34 x i8], [34 x i8]* @52, i32 0, i32 0))
  store float %tmp__Z23do_airspeed_calibrationf5, float* %diff_pres_filtered_pa, align 4
  call void @stg_update_store_float(float* %diff_pres_filtered_pa, i8* getelementptr inbounds ([34 x i8], [34 x i8]* @54, i32 0, i32 0))
  %tmp__Z23do_airspeed_calibrationf6 = load float, float* %diff_pres_filtered_pa, align 4
  call void @stg_update_load_float(float* %diff_pres_filtered_pa, i8* getelementptr inbounds ([34 x i8], [34 x i8]* @56, i32 0, i32 0))
  %cmp4 = fcmp ogt float %tmp__Z23do_airspeed_calibrationf6, 5.000000e+01
  call void @stg_update_op(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @57, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8], [34 x i8]* @58, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @59, i32 0, i32 0), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @60, i32 0, i32 0))
  call void @stg_update_pc(i1 %cmp4, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @61, i32 0, i32 0))
  br i1 %cmp4, label %if.then5, label %if.end

if.then5:                                         ; preds = %while.body
  store i32 1, i32* %successfulCalibration, align 4
  call void @stg_update_store(i32* %successfulCalibration, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @64, i32 0, i32 0))
  br label %while.end

if.end:                                           ; preds = %while.body
  %tmp__Z23do_airspeed_calibrationf7 = load float, float* %diff_pres_filtered_pa, align 4
  call void @stg_update_load_float(float* %diff_pres_filtered_pa, i8* getelementptr inbounds ([34 x i8], [34 x i8]* @67, i32 0, i32 0))
  %cmp6 = fcmp olt float %tmp__Z23do_airspeed_calibrationf7, 0.000000e+00
  call void @stg_update_op(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @68, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8], [34 x i8]* @69, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @70, i32 0, i32 0), i8* getelementptr inbounds ([9 x i8], [9 x i8]* @71, i32 0, i32 0))
  call void @stg_update_pc(i1 %cmp6, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @72, i32 0, i32 0))
  br i1 %cmp6, label %if.then7, label %if.end8

if.then7:                                         ; preds = %if.end
  store i32 0, i32* %successfulCalibration, align 4
  call void @stg_update_store(i32* %successfulCalibration, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @75, i32 0, i32 0))
  br label %while.end

if.end8:                                          ; preds = %if.end
  %tmp__Z23do_airspeed_calibrationf8 = load i32, i32* %calibration_counter, align 4
  call void @stg_update_load(i32* %calibration_counter, i8* getelementptr inbounds ([34 x i8], [34 x i8]* @78, i32 0, i32 0))
  %inc = add nsw i32 %tmp__Z23do_airspeed_calibrationf8, 1
  call void @stg_update_op(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @79, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8], [34 x i8]* @80, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @81, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @82, i32 0, i32 0))
  store i32 %inc, i32* %calibration_counter, align 4
  call void @stg_update_store(i32* %calibration_counter, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @84, i32 0, i32 0))
  br label %while.cond

while.end:                                        ; preds = %if.then7, %if.then5, %while.cond
  br label %if.end9

if.end9:                                          ; preds = %while.end, %if.then
  %tmp__Z23do_airspeed_calibrationf9 = load i32, i32* %calibration_counter, align 4
  call void @stg_update_load(i32* %calibration_counter, i8* getelementptr inbounds ([34 x i8], [34 x i8]* @88, i32 0, i32 0))
  %cmp10 = icmp eq i32 %tmp__Z23do_airspeed_calibrationf9, 5
  call void @stg_update_op(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @89, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8], [34 x i8]* @90, i32 0, i32 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @91, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @92, i32 0, i32 0))
  call void @stg_update_pc(i1 %cmp10, i8* getelementptr inbounds ([6 x i8], [6 x i8]* @93, i32 0, i32 0))
  br i1 %cmp10, label %if.then11, label %if.end12

if.then11:                                        ; preds = %if.end9
  store i32 0, i32* %successfulCalibration, align 4
  call void @stg_update_store(i32* %successfulCalibration, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @96, i32 0, i32 0))
  br label %if.end12

if.end12:                                         ; preds = %if.then11, %if.end9
  %tmp__Z23do_airspeed_calibrationf10 = load i32, i32* %successfulCalibration, align 4
  call void @stg_update_load(i32* %successfulCalibration, i8* getelementptr inbounds ([35 x i8], [35 x i8]* @99, i32 0, i32 0))
  %call13 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.1, i32 0, i32 0), i32 %tmp__Z23do_airspeed_calibrationf10)
  %tmp__Z23do_airspeed_calibrationf11 = load i32, i32* %successfulCalibration, align 4
  call void @stg_update_load(i32* %successfulCalibration, i8* getelementptr inbounds ([35 x i8], [35 x i8]* @101, i32 0, i32 0))
  %tobool = icmp ne i32 %tmp__Z23do_airspeed_calibrationf11, 0
  call void @stg_update_op(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @102, i32 0, i32 0), i8* getelementptr inbounds ([35 x i8], [35 x i8]* @103, i32 0, i32 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @104, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @105, i32 0, i32 0))
  call void @stg_update_char(i8* getelementptr inbounds ([33 x i8], [33 x i8]* @106, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @107, i32 0, i32 0))
  ret i1 %tobool
}

declare i32 @printf(i8*, ...) #1

; Function Attrs: noinline norecurse optnone ssp uwtable
define i32 @main() #2 {
entry:
  %valueArray = alloca [5 x float], align 16
  %valueArray1 = alloca [5 x float], align 16
  %tmp_main = bitcast [5 x float]* %valueArray to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 16 %tmp_main, i8* align 16 bitcast ([5 x float]* @__const.main.valueArray to i8*), i64 20, i1 false)
  %tmp_main1 = bitcast [5 x float]* %valueArray1 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 16 %tmp_main1, i8* align 16 bitcast ([5 x float]* @__const.main.valueArray1 to i8*), i64 20, i1 false)
  call void @stg_begin_test()
  call void @stg_symbolic_array(i8* bitcast ([5 x float]* @readAir to i8*), i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.2, i32 0, i32 0), i32 5, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.3, i32 0, i32 0))
  %arraydecay = getelementptr inbounds [5 x float], [5 x float]* %valueArray, i32 0, i32 0
  %tmp_main2 = bitcast float* %arraydecay to i8*
  call void @stg_input_array(i8* bitcast ([5 x float]* @readAir to i8*), i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.2, i32 0, i32 0), i32 5, i8* %tmp_main2)
  call void @stg_update_char(i8* getelementptr inbounds ([15 x i8], [15 x i8]* @115, i32 0, i32 0), i8* getelementptr inbounds ([9 x i8], [9 x i8]* @116, i32 0, i32 0))
  %call = call zeroext i1 @_Z23do_airspeed_calibrationf(float 1.000000e+00)
  call void @stg_update_char(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @117, i32 0, i32 0), i8* getelementptr inbounds ([33 x i8], [33 x i8]* @118, i32 0, i32 0))
  call void @stg_assert(i1 zeroext %call)
  call void @stg_end_test()
  call void @stg_begin_test()
  call void @stg_symbolic_array(i8* bitcast ([5 x float]* @readAir to i8*), i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.2, i32 0, i32 0), i32 5, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.3, i32 0, i32 0))
  %arraydecay1 = getelementptr inbounds [5 x float], [5 x float]* %valueArray1, i32 0, i32 0
  %tmp_main3 = bitcast float* %arraydecay1 to i8*
  call void @stg_input_array(i8* bitcast ([5 x float]* @readAir to i8*), i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.2, i32 0, i32 0), i32 5, i8* %tmp_main3)
  call void @stg_update_char(i8* getelementptr inbounds ([15 x i8], [15 x i8]* @121, i32 0, i32 0), i8* getelementptr inbounds ([9 x i8], [9 x i8]* @122, i32 0, i32 0))
  %call2 = call zeroext i1 @_Z23do_airspeed_calibrationf(float 1.000000e+00)
  call void @stg_update_char(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @123, i32 0, i32 0), i8* getelementptr inbounds ([33 x i8], [33 x i8]* @124, i32 0, i32 0))
  call void @stg_assert(i1 zeroext %call2)
  call void @stg_end_test()
  call void @stg_update_char(i8* getelementptr inbounds ([9 x i8], [9 x i8]* @125, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @126, i32 0, i32 0))
  ret i32 0
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #3

declare void @stg_begin_test() #1

declare void @stg_symbolic_array(i8*, i8*, i32, i8*) #1

declare void @stg_input_array(i8*, i8*, i32, i8*) #1

declare void @stg_assert(i1 zeroext) #1

declare void @stg_end_test() #1

declare void @stg_update_op(i8*, i8*, i8*, i8*)

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
