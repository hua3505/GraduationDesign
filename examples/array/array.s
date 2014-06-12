; ModuleID = 'array.c'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-f128:128:128-n8:16:32"
target triple = "i386-pc-linux-gnu"

%struct.person = type { [10 x i8], i32 }

@score = common unnamed_addr global [10 x i32] zeroinitializer, align 32
@pepole = common unnamed_addr global [10 x %struct.person] zeroinitializer, align 32
@g_apScore = common unnamed_addr global [4 x [10 x i32]*] zeroinitializer

define i32 @main() nounwind {
entry:
  %retval = alloca i32
  %0 = alloca i32
  %"alloca point" = bitcast i32 0 to i32
  store i32 1, i32* getelementptr inbounds ([10 x i32]* @score, i32 0, i32 0), align 4, !dbg !23
  store i32 0, i32* getelementptr inbounds ([10 x %struct.person]* @pepole, i32 0, i32 0, i32 1), align 4, !dbg !25
  store [10 x i32]* @score, [10 x i32]** getelementptr inbounds ([4 x [10 x i32]*]* @g_apScore, i32 0, i32 0), align 4, !dbg !26
  store i32 0, i32* %0, align 4, !dbg !27
  %1 = load i32* %0, align 4, !dbg !27
  store i32 %1, i32* %retval, align 4, !dbg !27
  br label %return, !dbg !27

return:                                           ; preds = %entry
  %retval1 = load i32* %retval, !dbg !27
  ret i32 %retval1, !dbg !27
}

!llvm.dbg.sp = !{!0}
!llvm.dbg.gv = !{!6, !10, !18}

!0 = metadata !{i32 589870, i32 0, metadata !1, metadata !"main", metadata !"main", metadata !"main", metadata !1, i32 14, metadata !3, i1 false, i1 true, i32 0, i32 0, null, i32 256, i1 false, i32 ()* @main} ; [ DW_TAG_subprogram ]
!1 = metadata !{i32 589865, metadata !"array.c", metadata !"/home/shaw/work/klee/examples/array/", metadata !2} ; [ DW_TAG_file_type ]
!2 = metadata !{i32 589841, i32 0, i32 1, metadata !"array.c", metadata !"/home/shaw/work/klee/examples/array/", metadata !"4.2.1 (Based on Apple Inc. build 5658) (LLVM build 2.9)", i1 true, i1 false, metadata !"", i32 0} ; [ DW_TAG_compile_unit ]
!3 = metadata !{i32 589845, metadata !1, metadata !"", metadata !1, i32 0, i64 0, i64 0, i64 0, i32 0, null, metadata !4, i32 0, null} ; [ DW_TAG_subroutine_type ]
!4 = metadata !{metadata !5}
!5 = metadata !{i32 589860, metadata !1, metadata !"int", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, i32 5} ; [ DW_TAG_base_type ]
!6 = metadata !{i32 589876, i32 0, metadata !1, metadata !"score", metadata !"score", metadata !"", metadata !1, i32 3, metadata !7, i1 false, i1 true, [10 x i32]* @score} ; [ DW_TAG_variable ]
!7 = metadata !{i32 589825, metadata !1, metadata !"", metadata !1, i32 0, i64 320, i64 32, i64 0, i32 0, metadata !5, metadata !8, i32 0, null} ; [ DW_TAG_array_type ]
!8 = metadata !{metadata !9}
!9 = metadata !{i32 589857, i64 0, i64 9}         ; [ DW_TAG_subrange_type ]
!10 = metadata !{i32 589876, i32 0, metadata !1, metadata !"pepole", metadata !"pepole", metadata !"", metadata !1, i32 9, metadata !11, i1 false, i1 true, [10 x %struct.person]* @pepole} ; [ DW_TAG_variable ]
!11 = metadata !{i32 589825, metadata !1, metadata !"", metadata !1, i32 0, i64 1280, i64 32, i64 0, i32 0, metadata !12, metadata !8, i32 0, null} ; [ DW_TAG_array_type ]
!12 = metadata !{i32 589843, metadata !1, metadata !"person", metadata !1, i32 6, i64 128, i64 32, i64 0, i32 0, null, metadata !13, i32 0, null} ; [ DW_TAG_structure_type ]
!13 = metadata !{metadata !14, metadata !17}
!14 = metadata !{i32 589837, metadata !12, metadata !"name", metadata !1, i32 7, i64 80, i64 8, i64 0, i32 0, metadata !15} ; [ DW_TAG_member ]
!15 = metadata !{i32 589825, metadata !1, metadata !"", metadata !1, i32 0, i64 80, i64 8, i64 0, i32 0, metadata !16, metadata !8, i32 0, null} ; [ DW_TAG_array_type ]
!16 = metadata !{i32 589860, metadata !1, metadata !"char", metadata !1, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!17 = metadata !{i32 589837, metadata !12, metadata !"sex", metadata !1, i32 8, i64 32, i64 32, i64 96, i32 0, metadata !5} ; [ DW_TAG_member ]
!18 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_apScore", metadata !"g_apScore", metadata !"", metadata !1, i32 11, metadata !19, i1 false, i1 true, [4 x [10 x i32]*]* @g_apScore} ; [ DW_TAG_variable ]
!19 = metadata !{i32 589825, metadata !1, metadata !"", metadata !1, i32 0, i64 128, i64 32, i64 0, i32 0, metadata !20, metadata !21, i32 0, null} ; [ DW_TAG_array_type ]
!20 = metadata !{i32 589839, metadata !1, metadata !"", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !7} ; [ DW_TAG_pointer_type ]
!21 = metadata !{metadata !22}
!22 = metadata !{i32 589857, i64 0, i64 3}        ; [ DW_TAG_subrange_type ]
!23 = metadata !{i32 15, i32 0, metadata !24, null}
!24 = metadata !{i32 589835, metadata !0, i32 14, i32 0, metadata !1, i32 0} ; [ DW_TAG_lexical_block ]
!25 = metadata !{i32 16, i32 0, metadata !24, null}
!26 = metadata !{i32 17, i32 0, metadata !24, null}
!27 = metadata !{i32 18, i32 0, metadata !24, null}
