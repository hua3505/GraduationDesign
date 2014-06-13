; ModuleID = 'malloc.o'
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
  store i8* %c, i8** %l_c, align 4, !dbg !68
  store i32* @g_iTest, i32** %l_pi, align 4, !dbg !70
  %0 = call noalias i8* @malloc(i32 10) nounwind, !dbg !71
  store i8* %0, i8** %l_str, align 4, !dbg !71
  %1 = load i8** %l_str, align 4, !dbg !72
  %2 = getelementptr inbounds i8* %1, i32 0, !dbg !72
  store i8 49, i8* %2, align 1, !dbg !72
  %3 = load i8** %l_str, align 4, !dbg !73
  %4 = getelementptr inbounds i8* %3, i32 0, !dbg !73
  %5 = load i8* %4, align 1, !dbg !73
  store i8 %5, i8* %c, align 1, !dbg !73
  %6 = load i8** %l_str, align 4, !dbg !74
  store i8* %6, i8** @g_str, align 4, !dbg !74
  %7 = load i8** @g_str, align 4, !dbg !75
  %8 = getelementptr inbounds i8* %7, i32 1, !dbg !75
  store i8 103, i8* %8, align 1, !dbg !75
  %9 = load i8** @g_str, align 4, !dbg !76
  %10 = getelementptr inbounds i8* %9, i32 1, !dbg !76
  %11 = load i8* %10, align 1, !dbg !76
  store i8 %11, i8* %c, align 1, !dbg !76
  %12 = load i8** %l_c, align 4, !dbg !77
  store i8 99, i8* %12, align 1, !dbg !77
  %13 = load i8** %l_c, align 4, !dbg !78
  %14 = load i8* %13, align 1, !dbg !78
  store i8 %14, i8* %cc, align 1, !dbg !78
  %15 = load i8** %l_c, align 4, !dbg !79
  store i8* %15, i8** @g_str, align 4, !dbg !79
  %16 = load i8** @g_str, align 4, !dbg !80
  store i8 103, i8* %16, align 1, !dbg !80
  %17 = load i32** %l_pi, align 4, !dbg !81
  store i32* %17, i32** @g_pi, align 4, !dbg !81
  %18 = load i32** @g_pi, align 4, !dbg !82
  store i32 9, i32* %18, align 4, !dbg !82
  %19 = load i32** %l_pi, align 4, !dbg !83
  store i32 10, i32* %19, align 4, !dbg !83
  %retval1 = load i32* %retval, !dbg !84
  ret i32 %retval1, !dbg !84
}

declare void @llvm.dbg.declare(metadata, metadata) nounwind readnone

declare noalias i8* @malloc(i32) nounwind

declare void @llvm.dbg.value(metadata, i64, metadata) nounwind readnone

!llvm.dbg.sp = !{!0, !6, !15, !24}
!llvm.dbg.gv = !{!34, !37, !38}
!llvm.dbg.lv.memcpy = !{!40, !41, !42, !43, !47}
!llvm.dbg.lv.memmove = !{!50, !51, !52, !53, !57}
!llvm.dbg.lv.memset = !{!60, !61, !62, !63}

!0 = metadata !{i32 589870, i32 0, metadata !1, metadata !"main", metadata !"main", metadata !"main", metadata !1, i32 8, metadata !3, i1 false, i1 true, i32 0, i32 0, null, i32 256, i1 false, i32 ()* @main} ; [ DW_TAG_subprogram ]
!1 = metadata !{i32 589865, metadata !"malloc.c", metadata !"/home/shaw/work/klee/examples/varInllvm/", metadata !2} ; [ DW_TAG_file_type ]
!2 = metadata !{i32 589841, i32 0, i32 1, metadata !"malloc.c", metadata !"/home/shaw/work/klee/examples/varInllvm/", metadata !"4.2.1 (Based on Apple Inc. build 5658) (LLVM build 2.9)", i1 true, i1 false, metadata !"", i32 0} ; [ DW_TAG_compile_unit ]
!3 = metadata !{i32 589845, metadata !1, metadata !"", metadata !1, i32 0, i64 0, i64 0, i64 0, i32 0, null, metadata !4, i32 0, null} ; [ DW_TAG_subroutine_type ]
!4 = metadata !{metadata !5}
!5 = metadata !{i32 589860, metadata !1, metadata !"int", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, i32 5} ; [ DW_TAG_base_type ]
!6 = metadata !{i32 589870, i32 0, metadata !7, metadata !"memcpy", metadata !"memcpy", metadata !"memcpy", metadata !7, i32 12, metadata !9, i1 false, i1 true, i32 0, i32 0, null, i32 256, i1 true, null} ; [ DW_TAG_subprogram ]
!7 = metadata !{i32 589865, metadata !"memcpy.c", metadata !"/home/shaw/work/klee/runtime/Intrinsic/", metadata !8} ; [ DW_TAG_file_type ]
!8 = metadata !{i32 589841, i32 0, i32 1, metadata !"memcpy.c", metadata !"/home/shaw/work/klee/runtime/Intrinsic/", metadata !"4.2.1 (Based on Apple Inc. build 5658) (LLVM build 2.9)", i1 true, i1 true, metadata !"", i32 0} ; [ DW_TAG_compile_unit ]
!9 = metadata !{i32 589845, metadata !7, metadata !"", metadata !7, i32 0, i64 0, i64 0, i64 0, i32 0, null, metadata !10, i32 0, null} ; [ DW_TAG_subroutine_type ]
!10 = metadata !{metadata !11, metadata !11, metadata !11, metadata !12}
!11 = metadata !{i32 589839, metadata !7, metadata !"", metadata !7, i32 0, i64 32, i64 32, i64 0, i32 0, null} ; [ DW_TAG_pointer_type ]
!12 = metadata !{i32 589846, metadata !13, metadata !"size_t", metadata !13, i32 326, i64 0, i64 0, i64 0, i32 0, metadata !14} ; [ DW_TAG_typedef ]
!13 = metadata !{i32 589865, metadata !"stddef.h", metadata !"/usr/lib/llvm-gcc-4.2-2.9-i686-linux/bin/../lib/gcc/i686-pc-linux-gnu/4.2.1/include", metadata !8} ; [ DW_TAG_file_type ]
!14 = metadata !{i32 589860, metadata !7, metadata !"unsigned int", metadata !7, i32 0, i64 32, i64 32, i64 0, i32 0, i32 7} ; [ DW_TAG_base_type ]
!15 = metadata !{i32 589870, i32 0, metadata !16, metadata !"memmove", metadata !"memmove", metadata !"memmove", metadata !16, i32 12, metadata !18, i1 false, i1 true, i32 0, i32 0, null, i32 256, i1 true, null} ; [ DW_TAG_subprogram ]
!16 = metadata !{i32 589865, metadata !"memmove.c", metadata !"/home/shaw/work/klee/runtime/Intrinsic/", metadata !17} ; [ DW_TAG_file_type ]
!17 = metadata !{i32 589841, i32 0, i32 1, metadata !"memmove.c", metadata !"/home/shaw/work/klee/runtime/Intrinsic/", metadata !"4.2.1 (Based on Apple Inc. build 5658) (LLVM build 2.9)", i1 true, i1 true, metadata !"", i32 0} ; [ DW_TAG_compile_unit ]
!18 = metadata !{i32 589845, metadata !16, metadata !"", metadata !16, i32 0, i64 0, i64 0, i64 0, i32 0, null, metadata !19, i32 0, null} ; [ DW_TAG_subroutine_type ]
!19 = metadata !{metadata !20, metadata !20, metadata !20, metadata !21}
!20 = metadata !{i32 589839, metadata !16, metadata !"", metadata !16, i32 0, i64 32, i64 32, i64 0, i32 0, null} ; [ DW_TAG_pointer_type ]
!21 = metadata !{i32 589846, metadata !22, metadata !"size_t", metadata !22, i32 326, i64 0, i64 0, i64 0, i32 0, metadata !23} ; [ DW_TAG_typedef ]
!22 = metadata !{i32 589865, metadata !"stddef.h", metadata !"/usr/lib/llvm-gcc-4.2-2.9-i686-linux/bin/../lib/gcc/i686-pc-linux-gnu/4.2.1/include", metadata !17} ; [ DW_TAG_file_type ]
!23 = metadata !{i32 589860, metadata !16, metadata !"unsigned int", metadata !16, i32 0, i64 32, i64 32, i64 0, i32 0, i32 7} ; [ DW_TAG_base_type ]
!24 = metadata !{i32 589870, i32 0, metadata !25, metadata !"memset", metadata !"memset", metadata !"memset", metadata !25, i32 12, metadata !27, i1 false, i1 true, i32 0, i32 0, null, i32 256, i1 true, null} ; [ DW_TAG_subprogram ]
!25 = metadata !{i32 589865, metadata !"memset.c", metadata !"/home/shaw/work/klee/runtime/Intrinsic/", metadata !26} ; [ DW_TAG_file_type ]
!26 = metadata !{i32 589841, i32 0, i32 1, metadata !"memset.c", metadata !"/home/shaw/work/klee/runtime/Intrinsic/", metadata !"4.2.1 (Based on Apple Inc. build 5658) (LLVM build 2.9)", i1 true, i1 true, metadata !"", i32 0} ; [ DW_TAG_compile_unit ]
!27 = metadata !{i32 589845, metadata !25, metadata !"", metadata !25, i32 0, i64 0, i64 0, i64 0, i32 0, null, metadata !28, i32 0, null} ; [ DW_TAG_subroutine_type ]
!28 = metadata !{metadata !29, metadata !29, metadata !30, metadata !31}
!29 = metadata !{i32 589839, metadata !25, metadata !"", metadata !25, i32 0, i64 32, i64 32, i64 0, i32 0, null} ; [ DW_TAG_pointer_type ]
!30 = metadata !{i32 589860, metadata !25, metadata !"int", metadata !25, i32 0, i64 32, i64 32, i64 0, i32 0, i32 5} ; [ DW_TAG_base_type ]
!31 = metadata !{i32 589846, metadata !32, metadata !"size_t", metadata !32, i32 326, i64 0, i64 0, i64 0, i32 0, metadata !33} ; [ DW_TAG_typedef ]
!32 = metadata !{i32 589865, metadata !"stddef.h", metadata !"/usr/lib/llvm-gcc-4.2-2.9-i686-linux/bin/../lib/gcc/i686-pc-linux-gnu/4.2.1/include", metadata !26} ; [ DW_TAG_file_type ]
!33 = metadata !{i32 589860, metadata !25, metadata !"unsigned int", metadata !25, i32 0, i64 32, i64 32, i64 0, i32 0, i32 7} ; [ DW_TAG_base_type ]
!34 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_str", metadata !"g_str", metadata !"", metadata !1, i32 3, metadata !35, i1 false, i1 true, i8** @g_str} ; [ DW_TAG_variable ]
!35 = metadata !{i32 589839, metadata !1, metadata !"", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !36} ; [ DW_TAG_pointer_type ]
!36 = metadata !{i32 589860, metadata !1, metadata !"char", metadata !1, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!37 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_iTest", metadata !"g_iTest", metadata !"", metadata !1, i32 4, metadata !5, i1 false, i1 true, i32* @g_iTest} ; [ DW_TAG_variable ]
!38 = metadata !{i32 589876, i32 0, metadata !1, metadata !"g_pi", metadata !"g_pi", metadata !"", metadata !1, i32 5, metadata !39, i1 false, i1 true, i32** @g_pi} ; [ DW_TAG_variable ]
!39 = metadata !{i32 589839, metadata !1, metadata !"", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !5} ; [ DW_TAG_pointer_type ]
!40 = metadata !{i32 590081, metadata !6, metadata !"destaddr", metadata !7, i32 12, metadata !11, i32 0} ; [ DW_TAG_arg_variable ]
!41 = metadata !{i32 590081, metadata !6, metadata !"srcaddr", metadata !7, i32 12, metadata !11, i32 0} ; [ DW_TAG_arg_variable ]
!42 = metadata !{i32 590081, metadata !6, metadata !"len", metadata !7, i32 12, metadata !12, i32 0} ; [ DW_TAG_arg_variable ]
!43 = metadata !{i32 590080, metadata !44, metadata !"dest", metadata !7, i32 13, metadata !45, i32 0} ; [ DW_TAG_auto_variable ]
!44 = metadata !{i32 589835, metadata !6, i32 12, i32 0, metadata !7, i32 0} ; [ DW_TAG_lexical_block ]
!45 = metadata !{i32 589839, metadata !7, metadata !"", metadata !7, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !46} ; [ DW_TAG_pointer_type ]
!46 = metadata !{i32 589860, metadata !7, metadata !"char", metadata !7, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!47 = metadata !{i32 590080, metadata !44, metadata !"src", metadata !7, i32 14, metadata !48, i32 0} ; [ DW_TAG_auto_variable ]
!48 = metadata !{i32 589839, metadata !7, metadata !"", metadata !7, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !49} ; [ DW_TAG_pointer_type ]
!49 = metadata !{i32 589862, metadata !7, metadata !"", metadata !7, i32 0, i64 8, i64 8, i64 0, i32 0, metadata !46} ; [ DW_TAG_const_type ]
!50 = metadata !{i32 590081, metadata !15, metadata !"dst", metadata !16, i32 12, metadata !20, i32 0} ; [ DW_TAG_arg_variable ]
!51 = metadata !{i32 590081, metadata !15, metadata !"src", metadata !16, i32 12, metadata !20, i32 0} ; [ DW_TAG_arg_variable ]
!52 = metadata !{i32 590081, metadata !15, metadata !"count", metadata !16, i32 12, metadata !21, i32 0} ; [ DW_TAG_arg_variable ]
!53 = metadata !{i32 590080, metadata !54, metadata !"a", metadata !16, i32 13, metadata !55, i32 0} ; [ DW_TAG_auto_variable ]
!54 = metadata !{i32 589835, metadata !15, i32 12, i32 0, metadata !16, i32 0} ; [ DW_TAG_lexical_block ]
!55 = metadata !{i32 589839, metadata !16, metadata !"", metadata !16, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !56} ; [ DW_TAG_pointer_type ]
!56 = metadata !{i32 589860, metadata !16, metadata !"char", metadata !16, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!57 = metadata !{i32 590080, metadata !54, metadata !"b", metadata !16, i32 14, metadata !58, i32 0} ; [ DW_TAG_auto_variable ]
!58 = metadata !{i32 589839, metadata !16, metadata !"", metadata !16, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !59} ; [ DW_TAG_pointer_type ]
!59 = metadata !{i32 589862, metadata !16, metadata !"", metadata !16, i32 0, i64 8, i64 8, i64 0, i32 0, metadata !56} ; [ DW_TAG_const_type ]
!60 = metadata !{i32 590081, metadata !24, metadata !"dst", metadata !25, i32 12, metadata !29, i32 0} ; [ DW_TAG_arg_variable ]
!61 = metadata !{i32 590081, metadata !24, metadata !"s", metadata !25, i32 12, metadata !30, i32 0} ; [ DW_TAG_arg_variable ]
!62 = metadata !{i32 590081, metadata !24, metadata !"count", metadata !25, i32 12, metadata !31, i32 0} ; [ DW_TAG_arg_variable ]
!63 = metadata !{i32 590080, metadata !64, metadata !"a", metadata !25, i32 13, metadata !65, i32 0} ; [ DW_TAG_auto_variable ]
!64 = metadata !{i32 589835, metadata !24, i32 12, i32 0, metadata !25, i32 0} ; [ DW_TAG_lexical_block ]
!65 = metadata !{i32 589839, metadata !25, metadata !"", metadata !25, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !66} ; [ DW_TAG_pointer_type ]
!66 = metadata !{i32 589877, metadata !25, metadata !"", metadata !25, i32 0, i64 8, i64 8, i64 0, i32 0, metadata !67} ; [ DW_TAG_volatile_type ]
!67 = metadata !{i32 589860, metadata !25, metadata !"char", metadata !25, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!68 = metadata !{i32 12, i32 0, metadata !69, null}
!69 = metadata !{i32 589835, metadata !0, i32 8, i32 0, metadata !1, i32 0} ; [ DW_TAG_lexical_block ]
!70 = metadata !{i32 13, i32 0, metadata !69, null}
!71 = metadata !{i32 15, i32 0, metadata !69, null}
!72 = metadata !{i32 16, i32 0, metadata !69, null}
!73 = metadata !{i32 17, i32 0, metadata !69, null}
!74 = metadata !{i32 18, i32 0, metadata !69, null}
!75 = metadata !{i32 19, i32 0, metadata !69, null}
!76 = metadata !{i32 20, i32 0, metadata !69, null}
!77 = metadata !{i32 21, i32 0, metadata !69, null}
!78 = metadata !{i32 22, i32 0, metadata !69, null}
!79 = metadata !{i32 23, i32 0, metadata !69, null}
!80 = metadata !{i32 24, i32 0, metadata !69, null}
!81 = metadata !{i32 27, i32 0, metadata !69, null}
!82 = metadata !{i32 28, i32 0, metadata !69, null}
!83 = metadata !{i32 29, i32 0, metadata !69, null}
!84 = metadata !{i32 31, i32 0, metadata !69, null}
