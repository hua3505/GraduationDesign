; ModuleID = 'test.c'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-f128:128:128-n8:16:32"
target triple = "i386-pc-linux-gnu"

@str = common unnamed_addr global [10 x i8] zeroinitializer
@pi = common unnamed_addr global i32* null
@a = common unnamed_addr global i32 0
@ai = common unnamed_addr global i32 0
@b = common unnamed_addr global float 0.000000e+00

define i32 @main() nounwind {
entry:
  %retval = alloca i32
  %0 = alloca i32
  %c = alloca i8
  %"alloca point" = bitcast i32 0 to i32
  call void @llvm.dbg.declare(metadata !{i8* %c}, metadata !17), !dbg !19
  store i8 104, i8* getelementptr inbounds ([10 x i8]* @str, i32 0, i32 1), align 1, !dbg !20
  %1 = load i8* getelementptr inbounds ([10 x i8]* @str, i32 0, i32 1), align 1, !dbg !21
  store i8 %1, i8* %c, align 1, !dbg !21
  store i32* @a, i32** @pi, align 4, !dbg !22
  %2 = load i32* @a, align 4, !dbg !23
  store i32 %2, i32* @ai, align 4, !dbg !23
  %3 = call noalias i8* @malloc(i32 4) nounwind, !dbg !24
  %4 = bitcast i8* %3 to i32*, !dbg !24
  store i32* %4, i32** @pi, align 4, !dbg !24
  %5 = load i32** @pi, align 4, !dbg !25
  store i32 100, i32* %5, align 4, !dbg !25
  %6 = load i32** @pi, align 4, !dbg !26
  store i32 234, i32* %6, align 4, !dbg !26
  store i32 0, i32* %0, align 4, !dbg !27
  %7 = load i32* %0, align 4, !dbg !27
  store i32 %7, i32* %retval, align 4, !dbg !27
  br label %return, !dbg !27

return:                                           ; preds = %entry
  %retval1 = load i32* %retval, !dbg !27
  ret i32 %retval1, !dbg !27
}

declare void @llvm.dbg.declare(metadata, metadata) nounwind readnone

declare noalias i8* @malloc(i32) nounwind

!llvm.dbg.sp = !{!0}
!llvm.dbg.gv = !{!6, !7, !8, !10, !15}

!0 = metadata !{i32 589870, i32 0, metadata !1, metadata !"main", metadata !"main", metadata !"main", metadata !1, i32 10, metadata !3, i1 false, i1 true, i32 0, i32 0, null, i32 256, i1 false, i32 ()* @main} ; [ DW_TAG_subprogram ]
!1 = metadata !{i32 589865, metadata !"test.c", metadata !"/home/shaw/work/klee/examples/test/", metadata !2} ; [ DW_TAG_file_type ]
!2 = metadata !{i32 589841, i32 0, i32 1, metadata !"test.c", metadata !"/home/shaw/work/klee/examples/test/", metadata !"4.2.1 (Based on Apple Inc. build 5658) (LLVM build 2.9)", i1 true, i1 false, metadata !"", i32 0} ; [ DW_TAG_compile_unit ]
!3 = metadata !{i32 589845, metadata !1, metadata !"", metadata !1, i32 0, i64 0, i64 0, i64 0, i32 0, null, metadata !4, i32 0, null} ; [ DW_TAG_subroutine_type ]
!4 = metadata !{metadata !5}
!5 = metadata !{i32 589860, metadata !1, metadata !"int", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, i32 5} ; [ DW_TAG_base_type ]
!6 = metadata !{i32 589876, i32 0, metadata !1, metadata !"a", metadata !"a", metadata !"", metadata !1, i32 3, metadata !5, i1 false, i1 true, i32* @a} ; [ DW_TAG_variable ]
!7 = metadata !{i32 589876, i32 0, metadata !1, metadata !"ai", metadata !"ai", metadata !"", metadata !1, i32 4, metadata !5, i1 false, i1 true, i32* @ai} ; [ DW_TAG_variable ]
!8 = metadata !{i32 589876, i32 0, metadata !1, metadata !"b", metadata !"b", metadata !"", metadata !1, i32 5, metadata !9, i1 false, i1 true, float* @b} ; [ DW_TAG_variable ]
!9 = metadata !{i32 589860, metadata !1, metadata !"float", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, i32 4} ; [ DW_TAG_base_type ]
!10 = metadata !{i32 589876, i32 0, metadata !1, metadata !"str", metadata !"str", metadata !"", metadata !1, i32 6, metadata !11, i1 false, i1 true, [10 x i8]* @str} ; [ DW_TAG_variable ]
!11 = metadata !{i32 589825, metadata !1, metadata !"", metadata !1, i32 0, i64 80, i64 8, i64 0, i32 0, metadata !12, metadata !13, i32 0, null} ; [ DW_TAG_array_type ]
!12 = metadata !{i32 589860, metadata !1, metadata !"char", metadata !1, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!13 = metadata !{metadata !14}
!14 = metadata !{i32 589857, i64 0, i64 9}        ; [ DW_TAG_subrange_type ]
!15 = metadata !{i32 589876, i32 0, metadata !1, metadata !"pi", metadata !"pi", metadata !"", metadata !1, i32 7, metadata !16, i1 false, i1 true, i32** @pi} ; [ DW_TAG_variable ]
!16 = metadata !{i32 589839, metadata !1, metadata !"", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !5} ; [ DW_TAG_pointer_type ]
!17 = metadata !{i32 590080, metadata !18, metadata !"c", metadata !1, i32 11, metadata !12, i32 0} ; [ DW_TAG_auto_variable ]
!18 = metadata !{i32 589835, metadata !0, i32 10, i32 0, metadata !1, i32 0} ; [ DW_TAG_lexical_block ]
!19 = metadata !{i32 11, i32 0, metadata !18, null}
!20 = metadata !{i32 12, i32 0, metadata !18, null}
!21 = metadata !{i32 13, i32 0, metadata !18, null}
!22 = metadata !{i32 14, i32 0, metadata !18, null}
!23 = metadata !{i32 15, i32 0, metadata !18, null}
!24 = metadata !{i32 16, i32 0, metadata !18, null}
!25 = metadata !{i32 17, i32 0, metadata !18, null}
!26 = metadata !{i32 18, i32 0, metadata !18, null}
!27 = metadata !{i32 19, i32 0, metadata !18, null}
