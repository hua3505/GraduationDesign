; ModuleID = 'test.o'
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
  %"alloca point" = bitcast i32 0 to i32
  store i32 1, i32* @iA, align 4, !dbg !78
  store i8 99, i8* @cA, align 1, !dbg !80
  store double 2.100000e+00, double* @lfA, align 8, !dbg !81
  store i32* @iA, i32** @ipB, align 4, !dbg !82
  store i32 1, i32* getelementptr inbounds ([5 x i32]* @iaB, i32 0, i32 0), align 4, !dbg !83
  store i32 1, i32* getelementptr inbounds (%struct.test* @testC, i32 0, i32 0), align 4, !dbg !84
  store i8 98, i8* getelementptr inbounds (%struct.test* @testC, i32 0, i32 1), align 4, !dbg !85
  %1 = call noalias i8* @malloc(i32 4) nounwind, !dbg !86
  %2 = bitcast i8* %1 to i32*, !dbg !86
  store i32* %2, i32** @ipB, align 4, !dbg !86
  %3 = load i32** @ipB, align 4, !dbg !87
  store i32 2, i32* %3, align 4, !dbg !87
  store i32 0, i32* %0, align 4, !dbg !88
  %4 = load i32* %0, align 4, !dbg !88
  store i32 %4, i32* %retval, align 4, !dbg !88
  %retval1 = load i32* %retval, !dbg !88
  ret i32 %retval1, !dbg !88
}

declare noalias i8* @malloc(i32) nounwind

declare void @llvm.dbg.value(metadata, i64, metadata) nounwind readnone

!llvm.dbg.sp = !{!0, !6, !15, !24}
!llvm.dbg.gv = !{!34, !35, !37, !39, !41, !45}
!llvm.dbg.lv.memcpy = !{!50, !51, !52, !53, !57}
!llvm.dbg.lv.memmove = !{!60, !61, !62, !63, !67}
!llvm.dbg.lv.memset = !{!70, !71, !72, !73}

!0 = metadata !{i32 589870, i32 0, metadata !1, metadata !"main", metadata !"main", metadata !"main", metadata !1, i32 15, metadata !3, i1 false, i1 true, i32 0, i32 0, null, i32 256, i1 false, i32 ()* @main} ; [ DW_TAG_subprogram ]
!1 = metadata !{i32 589865, metadata !"test.c", metadata !"/home/shaw/work/klee/examples/varInllvm/", metadata !2} ; [ DW_TAG_file_type ]
!2 = metadata !{i32 589841, i32 0, i32 1, metadata !"test.c", metadata !"/home/shaw/work/klee/examples/varInllvm/", metadata !"4.2.1 (Based on Apple Inc. build 5658) (LLVM build 2.9)", i1 true, i1 false, metadata !"", i32 0} ; [ DW_TAG_compile_unit ]
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
!34 = metadata !{i32 589876, i32 0, metadata !1, metadata !"iA", metadata !"iA", metadata !"", metadata !1, i32 3, metadata !5, i1 false, i1 true, i32* @iA} ; [ DW_TAG_variable ]
!35 = metadata !{i32 589876, i32 0, metadata !1, metadata !"cA", metadata !"cA", metadata !"", metadata !1, i32 4, metadata !36, i1 false, i1 true, i8* @cA} ; [ DW_TAG_variable ]
!36 = metadata !{i32 589860, metadata !1, metadata !"char", metadata !1, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!37 = metadata !{i32 589876, i32 0, metadata !1, metadata !"lfA", metadata !"lfA", metadata !"", metadata !1, i32 5, metadata !38, i1 false, i1 true, double* @lfA} ; [ DW_TAG_variable ]
!38 = metadata !{i32 589860, metadata !1, metadata !"double", metadata !1, i32 0, i64 64, i64 64, i64 0, i32 0, i32 4} ; [ DW_TAG_base_type ]
!39 = metadata !{i32 589876, i32 0, metadata !1, metadata !"ipB", metadata !"ipB", metadata !"", metadata !1, i32 6, metadata !40, i1 false, i1 true, i32** @ipB} ; [ DW_TAG_variable ]
!40 = metadata !{i32 589839, metadata !1, metadata !"", metadata !1, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !5} ; [ DW_TAG_pointer_type ]
!41 = metadata !{i32 589876, i32 0, metadata !1, metadata !"iaB", metadata !"iaB", metadata !"", metadata !1, i32 7, metadata !42, i1 false, i1 true, [5 x i32]* @iaB} ; [ DW_TAG_variable ]
!42 = metadata !{i32 589825, metadata !1, metadata !"", metadata !1, i32 0, i64 160, i64 32, i64 0, i32 0, metadata !5, metadata !43, i32 0, null} ; [ DW_TAG_array_type ]
!43 = metadata !{metadata !44}
!44 = metadata !{i32 589857, i64 0, i64 4}        ; [ DW_TAG_subrange_type ]
!45 = metadata !{i32 589876, i32 0, metadata !1, metadata !"testC", metadata !"testC", metadata !"", metadata !1, i32 12, metadata !46, i1 false, i1 true, %struct.test* @testC} ; [ DW_TAG_variable ]
!46 = metadata !{i32 589843, metadata !1, metadata !"test", metadata !1, i32 9, i64 64, i64 32, i64 0, i32 0, null, metadata !47, i32 0, null} ; [ DW_TAG_structure_type ]
!47 = metadata !{metadata !48, metadata !49}
!48 = metadata !{i32 589837, metadata !46, metadata !"_a", metadata !1, i32 10, i64 32, i64 32, i64 0, i32 0, metadata !5} ; [ DW_TAG_member ]
!49 = metadata !{i32 589837, metadata !46, metadata !"_b", metadata !1, i32 11, i64 8, i64 8, i64 32, i32 0, metadata !36} ; [ DW_TAG_member ]
!50 = metadata !{i32 590081, metadata !6, metadata !"destaddr", metadata !7, i32 12, metadata !11, i32 0} ; [ DW_TAG_arg_variable ]
!51 = metadata !{i32 590081, metadata !6, metadata !"srcaddr", metadata !7, i32 12, metadata !11, i32 0} ; [ DW_TAG_arg_variable ]
!52 = metadata !{i32 590081, metadata !6, metadata !"len", metadata !7, i32 12, metadata !12, i32 0} ; [ DW_TAG_arg_variable ]
!53 = metadata !{i32 590080, metadata !54, metadata !"dest", metadata !7, i32 13, metadata !55, i32 0} ; [ DW_TAG_auto_variable ]
!54 = metadata !{i32 589835, metadata !6, i32 12, i32 0, metadata !7, i32 0} ; [ DW_TAG_lexical_block ]
!55 = metadata !{i32 589839, metadata !7, metadata !"", metadata !7, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !56} ; [ DW_TAG_pointer_type ]
!56 = metadata !{i32 589860, metadata !7, metadata !"char", metadata !7, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!57 = metadata !{i32 590080, metadata !54, metadata !"src", metadata !7, i32 14, metadata !58, i32 0} ; [ DW_TAG_auto_variable ]
!58 = metadata !{i32 589839, metadata !7, metadata !"", metadata !7, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !59} ; [ DW_TAG_pointer_type ]
!59 = metadata !{i32 589862, metadata !7, metadata !"", metadata !7, i32 0, i64 8, i64 8, i64 0, i32 0, metadata !56} ; [ DW_TAG_const_type ]
!60 = metadata !{i32 590081, metadata !15, metadata !"dst", metadata !16, i32 12, metadata !20, i32 0} ; [ DW_TAG_arg_variable ]
!61 = metadata !{i32 590081, metadata !15, metadata !"src", metadata !16, i32 12, metadata !20, i32 0} ; [ DW_TAG_arg_variable ]
!62 = metadata !{i32 590081, metadata !15, metadata !"count", metadata !16, i32 12, metadata !21, i32 0} ; [ DW_TAG_arg_variable ]
!63 = metadata !{i32 590080, metadata !64, metadata !"a", metadata !16, i32 13, metadata !65, i32 0} ; [ DW_TAG_auto_variable ]
!64 = metadata !{i32 589835, metadata !15, i32 12, i32 0, metadata !16, i32 0} ; [ DW_TAG_lexical_block ]
!65 = metadata !{i32 589839, metadata !16, metadata !"", metadata !16, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !66} ; [ DW_TAG_pointer_type ]
!66 = metadata !{i32 589860, metadata !16, metadata !"char", metadata !16, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!67 = metadata !{i32 590080, metadata !64, metadata !"b", metadata !16, i32 14, metadata !68, i32 0} ; [ DW_TAG_auto_variable ]
!68 = metadata !{i32 589839, metadata !16, metadata !"", metadata !16, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !69} ; [ DW_TAG_pointer_type ]
!69 = metadata !{i32 589862, metadata !16, metadata !"", metadata !16, i32 0, i64 8, i64 8, i64 0, i32 0, metadata !66} ; [ DW_TAG_const_type ]
!70 = metadata !{i32 590081, metadata !24, metadata !"dst", metadata !25, i32 12, metadata !29, i32 0} ; [ DW_TAG_arg_variable ]
!71 = metadata !{i32 590081, metadata !24, metadata !"s", metadata !25, i32 12, metadata !30, i32 0} ; [ DW_TAG_arg_variable ]
!72 = metadata !{i32 590081, metadata !24, metadata !"count", metadata !25, i32 12, metadata !31, i32 0} ; [ DW_TAG_arg_variable ]
!73 = metadata !{i32 590080, metadata !74, metadata !"a", metadata !25, i32 13, metadata !75, i32 0} ; [ DW_TAG_auto_variable ]
!74 = metadata !{i32 589835, metadata !24, i32 12, i32 0, metadata !25, i32 0} ; [ DW_TAG_lexical_block ]
!75 = metadata !{i32 589839, metadata !25, metadata !"", metadata !25, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !76} ; [ DW_TAG_pointer_type ]
!76 = metadata !{i32 589877, metadata !25, metadata !"", metadata !25, i32 0, i64 8, i64 8, i64 0, i32 0, metadata !77} ; [ DW_TAG_volatile_type ]
!77 = metadata !{i32 589860, metadata !25, metadata !"char", metadata !25, i32 0, i64 8, i64 8, i64 0, i32 0, i32 6} ; [ DW_TAG_base_type ]
!78 = metadata !{i32 16, i32 0, metadata !79, null}
!79 = metadata !{i32 589835, metadata !0, i32 15, i32 0, metadata !1, i32 0} ; [ DW_TAG_lexical_block ]
!80 = metadata !{i32 17, i32 0, metadata !79, null}
!81 = metadata !{i32 18, i32 0, metadata !79, null}
!82 = metadata !{i32 19, i32 0, metadata !79, null}
!83 = metadata !{i32 20, i32 0, metadata !79, null}
!84 = metadata !{i32 21, i32 0, metadata !79, null}
!85 = metadata !{i32 22, i32 0, metadata !79, null}
!86 = metadata !{i32 23, i32 0, metadata !79, null}
!87 = metadata !{i32 24, i32 0, metadata !79, null}
!88 = metadata !{i32 25, i32 0, metadata !79, null}
