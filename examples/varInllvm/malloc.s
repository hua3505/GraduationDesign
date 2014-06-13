; ModuleID = 'malloc.c'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-f128:128:128-n8:16:32"
target triple = "i386-pc-linux-gnu"

@g_iTest = common unnamed_addr global i32 0
@g_str = common unnamed_addr global i8* null
@g_pi = common unnamed_addr global i32* null

define i32 @main() nounwind {
entry:
  %retval = alloca i32
  %l_str = alloca i8*
  %c = alloca i8
  %cc = alloca i8
  %l_c = alloca i8*
  %l_pi = alloca i32*
  %"alloca point" = bitcast i32 0 to i32
  call void @llvm.dbg.declare(metadata !{i8** %l_str}, metadata !12), !dbg !14
  call void @llvm.dbg.declare(metadata !{i8* %c}, metadata !15), !dbg !16
  call void @llvm.dbg.declare(metadata !{i8* %cc}, metadata !17), !dbg !18
  call void @llvm.dbg.declare(metadata !{i8** %l_c}, metadata !19), !dbg !20
  call void @llvm.dbg.declare(metadata !{i32** %l_pi}, metadata !21), !dbg !22
  store i8* %c, i8** %l_c, align 4, !dbg !20
  store i32* @g_iTest, i32** %l_pi, align 4, !dbg !22
  %0 = call noalias i8* @malloc(i32 10) nounwind, !dbg !23
  store i8* %0, i8** %l_str, align 4, !dbg !23
  %1 = load i8** %l_str, align 4, !dbg !24
  %2 = getelementptr inbounds i8* %1, i32 0, !dbg !24
  store i8 49, i8* %2, align 1, !dbg !24
  %3 = load i8** %l_str, align 4, !dbg !25
  %4 = getelementptr inbounds i8* %3, i32 0, !dbg !25
  %5 = load i8* %4, align 1, !dbg !25
  store i8 %5, i8* %c, align 1, !dbg !25
  %6 = load i8** %l_str, align 4, !dbg !26
  store i8* %6, i8** @g_str, align 4, !dbg !26
  %7 = load i8** @g_str, align 4, !dbg !27
  %8 = getelementptr inbounds i8* %7, i32 1, !dbg !27
  store i8 103, i8* %8, align 1, !dbg !27
  %9 = load i8** @g_str, align 4, !dbg !28
  %10 = getelementptr inbounds i8* %9, i32 1, !dbg !28
  %11 = load i8* %10, align 1, !dbg !28
  store i8 %11, i8* %c, align 1, !dbg !28
  %12 = load i8** %l_c, align 4, !dbg !29
  store i8 99, i8* %12, align 1, !dbg !29
  %13 = load i8** %l_c, align 4, !dbg !30
  %14 = load i8* %13, align 1, !dbg !30
  store i8 %14, i8* %cc, align 1, !dbg !30
  %15 = load i8** %l_c, align 4, !dbg !31
  store i8* %15, i8** @g_str, align 4, !dbg !31
  %16 = load i8** @g_str, align 4, !dbg !32
  store i8 103, i8* %16, align 1, !dbg !32
  %17 = load i32** %l_pi, align 4, !dbg !33
  store i32* %17, i32** @g_pi, align 4, !dbg !33
  %18 = load i32** @g_pi, align 4, !dbg !34
  store i32 9, i32* %18, align 4, !dbg !34
  %19 = load i32** %l_pi, align 4, !dbg !35
  store i32 10, i32* %19, align 4, !dbg !35
  br label %return, !dbg !36

return:                                           ; preds = %entry
  %retval1 = load i32* %retval, !dbg !36
  ret i32 %retval1, !dbg !36
}

declare void @llvm.dbg.declare(metadata, metadata) nounwind readnone

declare noalias i8* @malloc(i32) nounwind

!llvm.dbg.sp = !{!0}
!llvm.dbg.gv = !{!6, !9, !10}

!0 = metadata !{i32 589870, i32 0, metadata !1, metadata !"main", metadata !"main", metadata !"main", metadata !1, i32 8, metadata !3, i1 false, i1 true, i32 0, i32 0, null, i32 256, i1 false, i32 ()* @main} ; [ DW_TAG_subprogram ]
!1 = metadata !{i32 589865, metadata !"malloc.c", metadata !"/home/shaw/work/klee/examples/varInllvm/", metadata !2} ; [ DW_TAG_file_type ]
!2 = metadata !{i32 589841, i32 0, i32 1, metadata !"malloc.c", metadata !"/home/shaw/work/klee/examples/varInllvm/", metadata !"4.2.1 (Based on Apple Inc. build 5658) (LLVM build 2.9)", i1 true, i1 false, metadata !"", i32 0} ; [ DW_TAG_compile_unit ]
!3 = metadata !{i32 589845, metadata !1, metadata !"", metadata !1, i32 0, i64 0, i64 0, i64 0, i32 0, null, metadata !4, i32 0, null} ; [ DW_TAG_subroutine_type ]
!4 = metadata !{metadata !5}
!5 = metadata !{i32 589860, metadata !1, metadata !"int", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, i32 5} ; [ DW_TAG_base_type ]
!6 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_str", metadata !"g_str", metadata !"", metadata !1, i32 3, metadata !7, i1 false, i1 true, i8** @g_str} ; [ DW_TAG_variable ]
!7 = metadata !{i32 589839, metadata !1, metadata !"", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !8} ; [ DW_TAG_pointer_type ]
!8 = metadata !{i32 589860, metadata !1, metadata !"char", metadata !1, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!9 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_iTest", metadata !"g_iTest", metadata !"", metadata !1, i32 4, metadata !5, i1 false, i1 true, i32* @g_iTest} ; [ DW_TAG_variable ]
!10 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_pi", metadata !"g_pi", metadata !"", metadata !1, i32 5, metadata !11, i1 false, i1 true, i32** @g_pi} ; [ DW_TAG_variable ]
!11 = metadata !{i32 589839, metadata !1, metadata !"", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !5} ; [ DW_TAG_pointer_type ]
!12 = metadata !{i32 590080, metadata !13, metadata !"l_str", metadata !1, i32 9, metadata !7, i32 0} ; [ DW_TAG_auto_variable ]
!13 = metadata !{i32 589835, metadata !0, i32 8, i32 0, metadata !1, i32 0} ; [ DW_TAG_lexical_block ]
!14 = metadata !{i32 9, i32 0, metadata !13, null}
!15 = metadata !{i32 590080, metadata !13, metadata !"c", metadata !1, i32 10, metadata !8, i32 0} ; [ DW_TAG_auto_variable ]
!16 = metadata !{i32 10, i32 0, metadata !13, null}
!17 = metadata !{i32 590080, metadata !13, metadata !"cc", metadata !1, i32 11, metadata !8, i32 0} ; [ DW_TAG_auto_variable ]
!18 = metadata !{i32 11, i32 0, metadata !13, null}
!19 = metadata !{i32 590080, metadata !13, metadata !"l_c", metadata !1, i32 12, metadata !7, i32 0} ; [ DW_TAG_auto_variable ]
!20 = metadata !{i32 12, i32 0, metadata !13, null}
!21 = metadata !{i32 590080, metadata !13, metadata !"l_pi", metadata !1, i32 13, metadata !11, i32 0} ; [ DW_TAG_auto_variable ]
!22 = metadata !{i32 13, i32 0, metadata !13, null}
!23 = metadata !{i32 15, i32 0, metadata !13, null}
!24 = metadata !{i32 16, i32 0, metadata !13, null}
!25 = metadata !{i32 17, i32 0, metadata !13, null}
!26 = metadata !{i32 18, i32 0, metadata !13, null}
!27 = metadata !{i32 19, i32 0, metadata !13, null}
!28 = metadata !{i32 20, i32 0, metadata !13, null}
!29 = metadata !{i32 21, i32 0, metadata !13, null}
!30 = metadata !{i32 22, i32 0, metadata !13, null}
!31 = metadata !{i32 23, i32 0, metadata !13, null}
!32 = metadata !{i32 24, i32 0, metadata !13, null}
!33 = metadata !{i32 27, i32 0, metadata !13, null}
!34 = metadata !{i32 28, i32 0, metadata !13, null}
!35 = metadata !{i32 29, i32 0, metadata !13, null}
!36 = metadata !{i32 31, i32 0, metadata !13, null}
