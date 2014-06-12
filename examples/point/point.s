; ModuleID = 'point.c'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-f128:128:128-n8:16:32"
target triple = "i386-pc-linux-gnu"

%struct.person = type { [10 x i8], i32 }

@g_piToGlobal = unnamed_addr global i32* @g_iA
@g_iA = common unnamed_addr global i32 0
@g_paToArray = unnamed_addr global [10 x i32]* @g_iArray
@g_iArray = common unnamed_addr global [10 x i32] zeroinitializer, align 32
@g_pToPoint = unnamed_addr global i32** @g_piToGlobal
@g_pToStruct = unnamed_addr global %struct.person* @yan
@yan = common unnamed_addr global %struct.person zeroinitializer
@g_piToLocal = common unnamed_addr global i32* null
@.str = private unnamed_addr constant [4 x i8] c"yan\00", align 1
@.str1 = private unnamed_addr constant [3 x i8] c"%s\00", align 1

define i32 @main() nounwind {
entry:
  %retval = alloca i32
  %l_iA = alloca i32
  %l_iB = alloca i32
  %l_piToGocal = alloca i32*
  %"alloca point" = bitcast i32 0 to i32
  call void @llvm.dbg.declare(metadata !{i32* %l_iA}, metadata !27), !dbg !29
  call void @llvm.dbg.declare(metadata !{i32* %l_iB}, metadata !30), !dbg !31
  call void @llvm.dbg.declare(metadata !{i32** %l_piToGocal}, metadata !32), !dbg !33
  store i32* @g_iA, i32** %l_piToGocal, align 4, !dbg !33
  store i32* %l_iB, i32** @g_piToLocal, align 4, !dbg !34
  %0 = load i32** @g_piToLocal, align 4, !dbg !35
  store i32 11, i32* %0, align 4, !dbg !35
  %1 = load i32** @g_piToLocal, align 4, !dbg !36
  %2 = load i32* %1, align 4, !dbg !36
  store i32 %2, i32* %l_iA, align 4, !dbg !36
  %3 = load i32** @g_piToGlobal, align 4, !dbg !37
  store i32 12, i32* %3, align 4, !dbg !37
  %4 = load i32** @g_piToGlobal, align 4, !dbg !38
  %5 = load i32* %4, align 4, !dbg !38
  store i32 %5, i32* %l_iA, align 4, !dbg !38
  %6 = load i32** %l_piToGocal, align 4, !dbg !39
  store i32 13, i32* %6, align 4, !dbg !39
  %7 = load i32** %l_piToGocal, align 4, !dbg !40
  %8 = load i32* %7, align 4, !dbg !40
  store i32 %8, i32* %l_iA, align 4, !dbg !40
  %9 = load [10 x i32]** @g_paToArray, align 4, !dbg !41
  %10 = getelementptr inbounds [10 x i32]* %9, i32 0, i32 0, !dbg !41
  store i32 1, i32* %10, align 4, !dbg !41
  %11 = load [10 x i32]** @g_paToArray, align 4, !dbg !42
  %12 = getelementptr inbounds [10 x i32]* %11, i32 0, i32 0, !dbg !42
  %13 = load i32* %12, align 4, !dbg !42
  store i32 %13, i32* %l_iA, align 4, !dbg !42
  %14 = load i32*** @g_pToPoint, align 4, !dbg !43
  %15 = load i32** %14, align 4, !dbg !43
  store i32 2, i32* %15, align 4, !dbg !43
  %16 = load i32*** @g_pToPoint, align 4, !dbg !44
  %17 = load i32** %16, align 4, !dbg !44
  %18 = load i32* %17, align 4, !dbg !44
  store i32 %18, i32* %l_iA, align 4, !dbg !44
  %19 = load %struct.person** @g_pToStruct, align 4, !dbg !45
  %20 = getelementptr inbounds %struct.person* %19, i32 0, i32 0, !dbg !45
  %21 = getelementptr inbounds [10 x i8]* %20, i32 0, i32 0, !dbg !45
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %21, i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 4, i32 1, i1 false), !dbg !45
  %22 = load %struct.person** @g_pToStruct, align 4, !dbg !46
  %23 = getelementptr inbounds %struct.person* %22, i32 0, i32 0, !dbg !46
  %24 = getelementptr inbounds [10 x i8]* %23, i32 0, i32 0, !dbg !46
  %25 = call i32 (i8*, ...)* @printf(i8* noalias getelementptr inbounds ([3 x i8]* @.str1, i32 0, i32 0), i8* %24) nounwind, !dbg !46
  br label %return, !dbg !47

return:                                           ; preds = %entry
  %retval1 = load i32* %retval, !dbg !47
  ret i32 %retval1, !dbg !47
}

declare void @llvm.dbg.declare(metadata, metadata) nounwind readnone

declare void @llvm.memcpy.p0i8.p0i8.i32(i8* nocapture, i8* nocapture, i32, i32, i1) nounwind

declare i32 @printf(i8* noalias, ...) nounwind

!llvm.dbg.gv = !{!0, !5, !10, !12, !20, !21, !22, !23}
!llvm.dbg.sp = !{!24}

!0 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_piToGlobal", metadata !"g_piToGlobal", metadata !"", metadata !1, i32 5, metadata !3, i1 false, i1 true, i32** @g_piToGlobal} ; [ DW_TAG_variable ]
!1 = metadata !{i32 589865, metadata !"point.c", metadata !"/home/shaw/work/klee/examples/point/", metadata !2} ; [ DW_TAG_file_type ]
!2 = metadata !{i32 589841, i32 0, i32 1, metadata !"point.c", metadata !"/home/shaw/work/klee/examples/point/", metadata !"4.2.1 (Based on Apple Inc. build 5658) (LLVM build 2.9)", i1 true, i1 false, metadata !"", i32 0} ; [ DW_TAG_compile_unit ]
!3 = metadata !{i32 589839, metadata !1, metadata !"", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !4} ; [ DW_TAG_pointer_type ]
!4 = metadata !{i32 589860, metadata !1, metadata !"int", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, i32 5} ; [ DW_TAG_base_type ]
!5 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_paToArray", metadata !"g_paToArray", metadata !"", metadata !1, i32 9, metadata !6, i1 false, i1 true, [10 x i32]** @g_paToArray} ; [ DW_TAG_variable ]
!6 = metadata !{i32 589839, metadata !1, metadata !"", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !7} ; [ DW_TAG_pointer_type ]
!7 = metadata !{i32 589825, metadata !1, metadata !"", metadata !1, i32 0, i64 320, i64 32, i64 0, i32 0, metadata !4, metadata !8, i32 0, null} ; [ DW_TAG_array_type ]
!8 = metadata !{metadata !9}
!9 = metadata !{i32 589857, i64 0, i64 9}         ; [ DW_TAG_subrange_type ]
!10 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_pToPoint", metadata !"g_pToPoint", metadata !"", metadata !1, i32 10, metadata !11, i1 false, i1 true, i32*** @g_pToPoint} ; [ DW_TAG_variable ]
!11 = metadata !{i32 589839, metadata !1, metadata !"", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !3} ; [ DW_TAG_pointer_type ]
!12 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_pToStruct", metadata !"g_pToStruct", metadata !"", metadata !1, i32 14, metadata !13, i1 false, i1 true, %struct.person** @g_pToStruct} ; [ DW_TAG_variable ]
!13 = metadata !{i32 589839, metadata !1, metadata !"", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !14} ; [ DW_TAG_pointer_type ]
!14 = metadata !{i32 589843, metadata !1, metadata !"person", metadata !1, i32 11, i64 128, i64 32, i64 0, i32 0, null, metadata !15, i32 0, null} ; [ DW_TAG_structure_type ]
!15 = metadata !{metadata !16, metadata !19}
!16 = metadata !{i32 589837, metadata !14, metadata !"name", metadata !1, i32 12, i64 80, i64 8, i64 0, i32 0, metadata !17} ; [ DW_TAG_member ]
!17 = metadata !{i32 589825, metadata !1, metadata !"", metadata !1, i32 0, i64 80, i64 8, i64 0, i32 0, metadata !18, metadata !8, i32 0, null} ; [ DW_TAG_array_type ]
!18 = metadata !{i32 589860, metadata !1, metadata !"char", metadata !1, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!19 = metadata !{i32 589837, metadata !14, metadata !"sex", metadata !1, i32 13, i64 32, i64 32, i64 96, i32 0, metadata !4} ; [ DW_TAG_member ]
!20 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_iA", metadata !"g_iA", metadata !"", metadata !1, i32 4, metadata !4, i1 false, i1 true, i32* @g_iA} ; [ DW_TAG_variable ]
!21 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_piToLocal", metadata !"g_piToLocal", metadata !"", metadata !1, i32 6, metadata !3, i1 false, i1 true, i32** @g_piToLocal} ; [ DW_TAG_variable ]
!22 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_iArray", metadata !"g_iArray", metadata !"", metadata !1, i32 8, metadata !7, i1 false, i1 true, [10 x i32]* @g_iArray} ; [ DW_TAG_variable ]
!23 = metadata !{i32 589876, i32 0, metadata !1, metadata !"yan", metadata !"yan", metadata !"", metadata !1, i32 14, metadata !14, i1 false, i1 true, %struct.person* @yan} ; [ DW_TAG_variable ]
!24 = metadata !{i32 589870, i32 0, metadata !1, metadata !"main", metadata !"main", metadata !"main", metadata !1, i32 17, metadata !25, i1 false, i1 true, i32 0, i32 0, null, i32 256, i1 false, i32 ()* @main} ; [ DW_TAG_subprogram ]
!25 = metadata !{i32 589845, metadata !1, metadata !"", metadata !1, i32 0, i64 0, i64 0, i64 0, i32 0, null, metadata !26, i32 0, null} ; [ DW_TAG_subroutine_type ]
!26 = metadata !{metadata !4}
!27 = metadata !{i32 590080, metadata !28, metadata !"l_iA", metadata !1, i32 18, metadata !4, i32 0} ; [ DW_TAG_auto_variable ]
!28 = metadata !{i32 589835, metadata !24, i32 17, i32 0, metadata !1, i32 0} ; [ DW_TAG_lexical_block ]
!29 = metadata !{i32 18, i32 0, metadata !28, null}
!30 = metadata !{i32 590080, metadata !28, metadata !"l_iB", metadata !1, i32 19, metadata !4, i32 0} ; [ DW_TAG_auto_variable ]
!31 = metadata !{i32 19, i32 0, metadata !28, null}
!32 = metadata !{i32 590080, metadata !28, metadata !"l_piToGocal", metadata !1, i32 20, metadata !3, i32 0} ; [ DW_TAG_auto_variable ]
!33 = metadata !{i32 20, i32 0, metadata !28, null}
!34 = metadata !{i32 23, i32 0, metadata !28, null}
!35 = metadata !{i32 24, i32 0, metadata !28, null}
!36 = metadata !{i32 25, i32 0, metadata !28, null}
!37 = metadata !{i32 28, i32 0, metadata !28, null}
!38 = metadata !{i32 29, i32 0, metadata !28, null}
!39 = metadata !{i32 32, i32 0, metadata !28, null}
!40 = metadata !{i32 33, i32 0, metadata !28, null}
!41 = metadata !{i32 36, i32 0, metadata !28, null}
!42 = metadata !{i32 37, i32 0, metadata !28, null}
!43 = metadata !{i32 40, i32 0, metadata !28, null}
!44 = metadata !{i32 41, i32 0, metadata !28, null}
!45 = metadata !{i32 44, i32 0, metadata !28, null}
!46 = metadata !{i32 45, i32 0, metadata !28, null}
!47 = metadata !{i32 46, i32 0, metadata !28, null}
