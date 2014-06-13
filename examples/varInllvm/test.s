; ModuleID = 'test.c'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-f128:128:128-n8:16:32"
target triple = "i386-pc-linux-gnu"

%struct.test = type { i32, i8 }

@iA = common unnamed_addr global i32 0
@cA = common unnamed_addr global i8 0
@lfA = common unnamed_addr global double 0.000000e+00, align 8
@ipB = common unnamed_addr global i32* null
@iaB = common unnamed_addr global [5 x i32] zeroinitializer
@testC = common unnamed_addr global %struct.test zeroinitializer

define i32 @main() nounwind {
entry:
  %retval = alloca i32
  %0 = alloca i32
  %ipC = alloca i32*
  %"alloca point" = bitcast i32 0 to i32
  call void @llvm.dbg.declare(metadata !{i32** %ipC}, metadata !22), !dbg !24
  store i32 1, i32* @iA, align 4, !dbg !25
  store i8 99, i8* @cA, align 1, !dbg !26
  store double 2.100000e+00, double* @lfA, align 8, !dbg !27
  store i32* @iA, i32** @ipB, align 4, !dbg !28
  store i32 1, i32* getelementptr inbounds ([5 x i32]* @iaB, i32 0, i32 0), align 4, !dbg !29
  store i32 1, i32* getelementptr inbounds (%struct.test* @testC, i32 0, i32 0), align 4, !dbg !30
  store i8 98, i8* getelementptr inbounds (%struct.test* @testC, i32 0, i32 1), align 4, !dbg !31
  %1 = call noalias i8* @malloc(i32 4) nounwind, !dbg !32
  %2 = bitcast i8* %1 to i32*, !dbg !32
  store i32* %2, i32** @ipB, align 4, !dbg !32
  %3 = load i32** @ipB, align 4, !dbg !33
  store i32* %3, i32** %ipC, align 4, !dbg !33
  %4 = load i32** %ipC, align 4, !dbg !34
  store i32 2, i32* %4, align 4, !dbg !34
  %5 = load i32** @ipB, align 4, !dbg !35
  store i32 3, i32* %5, align 4, !dbg !35
  store i32 0, i32* %0, align 4, !dbg !36
  %6 = load i32* %0, align 4, !dbg !36
  store i32 %6, i32* %retval, align 4, !dbg !36
  br label %return, !dbg !36

return:                                           ; preds = %entry
  %retval1 = load i32* %retval, !dbg !36
  ret i32 %retval1, !dbg !36
}

declare void @llvm.dbg.declare(metadata, metadata) nounwind readnone

declare noalias i8* @malloc(i32) nounwind

!llvm.dbg.sp = !{!0}
!llvm.dbg.gv = !{!6, !7, !9, !11, !13, !17}

!0 = metadata !{i32 589870, i32 0, metadata !1, metadata !"main", metadata !"main", metadata !"main", metadata !1, i32 15, metadata !3, i1 false, i1 true, i32 0, i32 0, null, i32 256, i1 false, i32 ()* @main} ; [ DW_TAG_subprogram ]
!1 = metadata !{i32 589865, metadata !"test.c", metadata !"/home/shaw/work/klee/examples/varInllvm/", metadata !2} ; [ DW_TAG_file_type ]
!2 = metadata !{i32 589841, i32 0, i32 1, metadata !"test.c", metadata !"/home/shaw/work/klee/examples/varInllvm/", metadata !"4.2.1 (Based on Apple Inc. build 5658) (LLVM build 2.9)", i1 true, i1 false, metadata !"", i32 0} ; [ DW_TAG_compile_unit ]
!3 = metadata !{i32 589845, metadata !1, metadata !"", metadata !1, i32 0, i64 0, i64 0, i64 0, i32 0, null, metadata !4, i32 0, null} ; [ DW_TAG_subroutine_type ]
!4 = metadata !{metadata !5}
!5 = metadata !{i32 589860, metadata !1, metadata !"int", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, i32 5} ; [ DW_TAG_base_type ]
!6 = metadata !{i32 589876, i32 0, metadata !1, metadata !"iA", metadata !"iA", metadata !"", metadata !1, i32 3, metadata !5, i1 false, i1 true, i32* @iA} ; [ DW_TAG_variable ]
!7 = metadata !{i32 589876, i32 0, metadata !1, metadata !"cA", metadata !"cA", metadata !"", metadata !1, i32 4, metadata !8, i1 false, i1 true, i8* @cA} ; [ DW_TAG_variable ]
!8 = metadata !{i32 589860, metadata !1, metadata !"char", metadata !1, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!9 = metadata !{i32 589876, i32 0, metadata !1, metadata !"lfA", metadata !"lfA", metadata !"", metadata !1, i32 5, metadata !10, i1 false, i1 true, double* @lfA} ; [ DW_TAG_variable ]
!10 = metadata !{i32 589860, metadata !1, metadata !"double", metadata !1, i32 0, i64 64, i64 64, i64 0, i32 0, i32 4} ; [ DW_TAG_base_type ]
!11 = metadata !{i32 589876, i32 0, metadata !1, metadata !"ipB", metadata !"ipB", metadata !"", metadata !1, i32 6, metadata !12, i1 false, i1 true, i32** @ipB} ; [ DW_TAG_variable ]
!12 = metadata !{i32 589839, metadata !1, metadata !"", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !5} ; [ DW_TAG_pointer_type ]
!13 = metadata !{i32 589876, i32 0, metadata !1, metadata !"iaB", metadata !"iaB", metadata !"", metadata !1, i32 7, metadata !14, i1 false, i1 true, [5 x i32]* @iaB} ; [ DW_TAG_variable ]
!14 = metadata !{i32 589825, metadata !1, metadata !"", metadata !1, i32 0, i64 160, i64 32, i64 0, i32 0, metadata !5, metadata !15, i32 0, null} ; [ DW_TAG_array_type ]
!15 = metadata !{metadata !16}
!16 = metadata !{i32 589857, i64 0, i64 4}        ; [ DW_TAG_subrange_type ]
!17 = metadata !{i32 589876, i32 0, metadata !1, metadata !"testC", metadata !"testC", metadata !"", metadata !1, i32 12, metadata !18, i1 false, i1 true, %struct.test* @testC} ; [ DW_TAG_variable ]
!18 = metadata !{i32 589843, metadata !1, metadata !"test", metadata !1, i32 9, i64 64, i64 32, i64 0, i32 0, null, metadata !19, i32 0, null} ; [ DW_TAG_structure_type ]
!19 = metadata !{metadata !20, metadata !21}
!20 = metadata !{i32 589837, metadata !18, metadata !"_a", metadata !1, i32 10, i64 32, i64 32, i64 0, i32 0, metadata !5} ; [ DW_TAG_member ]
!21 = metadata !{i32 589837, metadata !18, metadata !"_b", metadata !1, i32 11, i64 8, i64 8, i64 32, i32 0, metadata !8} ; [ DW_TAG_member ]
!22 = metadata !{i32 590080, metadata !23, metadata !"ipC", metadata !1, i32 16, metadata !12, i32 0} ; [ DW_TAG_auto_variable ]
!23 = metadata !{i32 589835, metadata !0, i32 15, i32 0, metadata !1, i32 0} ; [ DW_TAG_lexical_block ]
!24 = metadata !{i32 16, i32 0, metadata !23, null}
!25 = metadata !{i32 17, i32 0, metadata !23, null}
!26 = metadata !{i32 18, i32 0, metadata !23, null}
!27 = metadata !{i32 19, i32 0, metadata !23, null}
!28 = metadata !{i32 20, i32 0, metadata !23, null}
!29 = metadata !{i32 21, i32 0, metadata !23, null}
!30 = metadata !{i32 22, i32 0, metadata !23, null}
!31 = metadata !{i32 23, i32 0, metadata !23, null}
!32 = metadata !{i32 24, i32 0, metadata !23, null}
!33 = metadata !{i32 25, i32 0, metadata !23, null}
!34 = metadata !{i32 26, i32 0, metadata !23, null}
!35 = metadata !{i32 27, i32 0, metadata !23, null}
!36 = metadata !{i32 28, i32 0, metadata !23, null}
