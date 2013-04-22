; ModuleID = 'text_example.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

@out = common global i32* null, align 4

define i32 @gcd(i32 %a_i, i32 %c) nounwind {
entry:
  %a_i.addr = alloca i32, align 4
  %c.addr = alloca i32, align 4
  %m = alloca i32, align 4
  %n = alloca i32, align 4
  store i32 %a_i, i32* %a_i.addr, align 4
  call void @llvm.dbg.declare(metadata !{i32* %a_i.addr}, metadata !17), !dbg !18
  store i32 %c, i32* %c.addr, align 4
  call void @llvm.dbg.declare(metadata !{i32* %c.addr}, metadata !19), !dbg !18
  call void @llvm.dbg.declare(metadata !{i32* %m}, metadata !20), !dbg !22
  call void @llvm.dbg.declare(metadata !{i32* %n}, metadata !23), !dbg !22
  %0 = load i32* %a_i.addr, align 4, !dbg !24
  %call = call i32 @abs(i32 %0) nounwind readnone, !dbg !24
  store i32 %call, i32* %m, align 4, !dbg !24
  %1 = load i32* %c.addr, align 4, !dbg !25
  %call1 = call i32 @abs(i32 %1) nounwind readnone, !dbg !25
  store i32 %call1, i32* %n, align 4, !dbg !25
  %2 = load i32* %m, align 4, !dbg !26
  %cmp = icmp eq i32 %2, 0, !dbg !26
  br i1 %cmp, label %if.then, label %if.else, !dbg !26

if.then:                                          ; preds = %entry
  store i32 1073741823, i32* %m, align 4, !dbg !27
  br label %if.end10, !dbg !29

if.else:                                          ; preds = %entry
  %3 = load i32* %n, align 4, !dbg !30
  %cmp2 = icmp ne i32 %3, 0, !dbg !30
  br i1 %cmp2, label %if.then3, label %if.end9, !dbg !30

if.then3:                                         ; preds = %if.else
  br label %while.cond, !dbg !31

while.cond:                                       ; preds = %if.end, %if.then3
  %4 = load i32* %m, align 4, !dbg !31
  %5 = load i32* %n, align 4, !dbg !31
  %cmp4 = icmp ne i32 %4, %5, !dbg !31
  br i1 %cmp4, label %while.body, label %while.end, !dbg !31

while.body:                                       ; preds = %while.cond
  %6 = load i32* %m, align 4, !dbg !33
  %7 = load i32* %n, align 4, !dbg !33
  %cmp5 = icmp sgt i32 %6, %7, !dbg !33
  br i1 %cmp5, label %if.then6, label %if.else7, !dbg !33

if.then6:                                         ; preds = %while.body
  %8 = load i32* %m, align 4, !dbg !35
  %9 = load i32* %n, align 4, !dbg !35
  %sub = sub nsw i32 %8, %9, !dbg !35
  store i32 %sub, i32* %m, align 4, !dbg !35
  br label %if.end, !dbg !35

if.else7:                                         ; preds = %while.body
  %10 = load i32* %n, align 4, !dbg !36
  %11 = load i32* %m, align 4, !dbg !36
  %sub8 = sub nsw i32 %10, %11, !dbg !36
  store i32 %sub8, i32* %n, align 4, !dbg !36
  br label %if.end

if.end:                                           ; preds = %if.else7, %if.then6
  br label %while.cond, !dbg !37

while.end:                                        ; preds = %while.cond
  br label %if.end9, !dbg !38

if.end9:                                          ; preds = %while.end, %if.else
  br label %if.end10

if.end10:                                         ; preds = %if.end9, %if.then
  %12 = load i32* %m, align 4, !dbg !39
  ret i32 %12, !dbg !39
}

declare void @llvm.dbg.declare(metadata, metadata) nounwind readnone

declare i32 @abs(i32) nounwind readnone

define i32 @get_gcd_sum(i32* %a, i32 %a_len, i32 %c) nounwind {
entry:
  %a.addr = alloca i32*, align 4
  %a_len.addr = alloca i32, align 4
  %c.addr = alloca i32, align 4
  %gsum = alloca i32, align 4
  %i = alloca i32, align 4
  %j = alloca i32, align 4
  store i32* %a, i32** %a.addr, align 4
  call void @llvm.dbg.declare(metadata !{i32** %a.addr}, metadata !40), !dbg !41
  store i32 %a_len, i32* %a_len.addr, align 4
  call void @llvm.dbg.declare(metadata !{i32* %a_len.addr}, metadata !42), !dbg !41
  store i32 %c, i32* %c.addr, align 4
  call void @llvm.dbg.declare(metadata !{i32* %c.addr}, metadata !43), !dbg !41
  call void @llvm.dbg.declare(metadata !{i32* %gsum}, metadata !44), !dbg !46
  call void @llvm.dbg.declare(metadata !{i32* %i}, metadata !47), !dbg !46
  call void @llvm.dbg.declare(metadata !{i32* %j}, metadata !48), !dbg !46
  %0 = load i32** %a.addr, align 4, !dbg !49
  %tobool = icmp ne i32* %0, null, !dbg !49
  br i1 %tobool, label %lor.lhs.false, label %if.then, !dbg !49

lor.lhs.false:                                    ; preds = %entry
  %1 = load i32* %a_len.addr, align 4, !dbg !49
  %cmp = icmp eq i32 %1, 0, !dbg !49
  br i1 %cmp, label %if.then, label %if.else, !dbg !49

if.then:                                          ; preds = %lor.lhs.false, %entry
  %2 = load i32* %c.addr, align 4, !dbg !50
  store i32 %2, i32* %gsum, align 4, !dbg !50
  br label %if.end7, !dbg !52

if.else:                                          ; preds = %lor.lhs.false
  %3 = load i32** %a.addr, align 4, !dbg !53
  %arrayidx = getelementptr inbounds i32* %3, i32 0, !dbg !53
  %4 = load i32* %arrayidx, align 4, !dbg !53
  %cmp1 = icmp eq i32 %4, 0, !dbg !53
  br i1 %cmp1, label %land.lhs.true, label %if.else4, !dbg !53

land.lhs.true:                                    ; preds = %if.else
  %5 = load i32* %c.addr, align 4, !dbg !53
  %cmp2 = icmp eq i32 %5, 0, !dbg !53
  br i1 %cmp2, label %if.then3, label %if.else4, !dbg !53

if.then3:                                         ; preds = %land.lhs.true
  store i32 1073741823, i32* %gsum, align 4, !dbg !54
  br label %if.end, !dbg !56

if.else4:                                         ; preds = %land.lhs.true, %if.else
  store i32 0, i32* %gsum, align 4, !dbg !57
  store i32 0, i32* %i, align 4, !dbg !59
  br label %for.cond, !dbg !59

for.cond:                                         ; preds = %for.inc, %if.else4
  %6 = load i32* %i, align 4, !dbg !59
  %7 = load i32* %a_len.addr, align 4, !dbg !59
  %cmp5 = icmp slt i32 %6, %7, !dbg !59
  br i1 %cmp5, label %for.body, label %for.end, !dbg !59

for.body:                                         ; preds = %for.cond
  %8 = load i32* %gsum, align 4, !dbg !61
  %9 = load i32* %i, align 4, !dbg !61
  %10 = load i32** %a.addr, align 4, !dbg !61
  %arrayidx6 = getelementptr inbounds i32* %10, i32 %9, !dbg !61
  %11 = load i32* %arrayidx6, align 4, !dbg !61
  %12 = load i32* %c.addr, align 4, !dbg !61
  %call = call i32 @gcd(i32 %11, i32 %12), !dbg !61
  %add = add nsw i32 %8, %call, !dbg !61
  store i32 %add, i32* %gsum, align 4, !dbg !61
  br label %for.inc, !dbg !63

for.inc:                                          ; preds = %for.body
  %13 = load i32* %i, align 4, !dbg !59
  %inc = add nsw i32 %13, 1, !dbg !59
  store i32 %inc, i32* %i, align 4, !dbg !59
  br label %for.cond, !dbg !59

for.end:                                          ; preds = %for.cond
  br label %if.end

if.end:                                           ; preds = %for.end, %if.then3
  br label %if.end7

if.end7:                                          ; preds = %if.end, %if.then
  %14 = load i32* %c.addr, align 4, !dbg !64
  %rem = srem i32 %14, 10, !dbg !64
  store i32 %rem, i32* %j, align 4, !dbg !64
  %15 = load i32* %gsum, align 4, !dbg !65
  %16 = load i32* %c.addr, align 4, !dbg !65
  %div = sdiv i32 %15, %16, !dbg !65
  %17 = load i32* %j, align 4, !dbg !65
  %18 = load i32** @out, align 4, !dbg !65
  %arrayidx8 = getelementptr inbounds i32* %18, i32 %17, !dbg !65
  store i32 %div, i32* %arrayidx8, align 4, !dbg !65
  %19 = load i32* %gsum, align 4, !dbg !66
  ret i32 %19, !dbg !66
}

!llvm.dbg.cu = !{!0}

!0 = metadata !{i32 786449, i32 0, i32 12, metadata !"text_example.c", metadata !"/home/qifcore/llvm-3.2/examples/QIF/CIF", metadata !"clang version 3.2 (tags/RELEASE_32/final)", i1 true, i1 false, metadata !"", i32 0, metadata !1, metadata !1, metadata !3, metadata !14} ; [ DW_TAG_compile_unit ] [/home/qifcore/llvm-3.2/examples/QIF/CIF/text_example.c] [DW_LANG_C99]
!1 = metadata !{metadata !2}
!2 = metadata !{i32 0}
!3 = metadata !{metadata !4}
!4 = metadata !{metadata !5, metadata !10}
!5 = metadata !{i32 786478, i32 0, metadata !6, metadata !"gcd", metadata !"gcd", metadata !"", metadata !6, i32 10, metadata !7, i1 false, i1 true, i32 0, i32 0, null, i32 0, i1 false, i32 (i32, i32)* @gcd, null, null, metadata !1, i32 11} ; [ DW_TAG_subprogram ] [line 10] [def] [scope 11] [gcd]
!6 = metadata !{i32 786473, metadata !"text_example.c", metadata !"/home/qifcore/llvm-3.2/examples/QIF/CIF", null} ; [ DW_TAG_file_type ]
!7 = metadata !{i32 786453, i32 0, metadata !"", i32 0, i32 0, i64 0, i64 0, i64 0, i32 0, null, metadata !8, i32 0, i32 0} ; [ DW_TAG_subroutine_type ] [line 0, size 0, align 0, offset 0] [from ]
!8 = metadata !{metadata !9, metadata !9, metadata !9}
!9 = metadata !{i32 786468, null, metadata !"int", null, i32 0, i64 32, i64 32, i64 0, i32 0, i32 5} ; [ DW_TAG_base_type ] [int] [line 0, size 32, align 32, offset 0, enc DW_ATE_signed]
!10 = metadata !{i32 786478, i32 0, metadata !6, metadata !"get_gcd_sum", metadata !"get_gcd_sum", metadata !"", metadata !6, i32 31, metadata !11, i1 false, i1 true, i32 0, i32 0, null, i32 256, i1 false, i32 (i32*, i32, i32)* @get_gcd_sum, null, null, metadata !1, i32 31} ; [ DW_TAG_subprogram ] [line 31] [def] [get_gcd_sum]
!11 = metadata !{i32 786453, i32 0, metadata !"", i32 0, i32 0, i64 0, i64 0, i64 0, i32 0, null, metadata !12, i32 0, i32 0} ; [ DW_TAG_subroutine_type ] [line 0, size 0, align 0, offset 0] [from ]
!12 = metadata !{metadata !9, metadata !13, metadata !9, metadata !9}
!13 = metadata !{i32 786447, null, metadata !"", null, i32 0, i64 32, i64 32, i64 0, i32 0, metadata !9} ; [ DW_TAG_pointer_type ] [line 0, size 32, align 32, offset 0] [from int]
!14 = metadata !{metadata !15}
!15 = metadata !{metadata !16}
!16 = metadata !{i32 786484, i32 0, null, metadata !"out", metadata !"out", metadata !"", metadata !6, i32 5, metadata !13, i32 0, i32 1, i32** @out} ; [ DW_TAG_variable ] [out] [line 5] [def]
!17 = metadata !{i32 786689, metadata !5, metadata !"a_i", metadata !6, i32 16777226, metadata !9, i32 0, i32 0} ; [ DW_TAG_arg_variable ] [a_i] [line 10]
!18 = metadata !{i32 10, i32 0, metadata !5, null}
!19 = metadata !{i32 786689, metadata !5, metadata !"c", metadata !6, i32 33554442, metadata !9, i32 0, i32 0} ; [ DW_TAG_arg_variable ] [c] [line 10]
!20 = metadata !{i32 786688, metadata !21, metadata !"m", metadata !6, i32 12, metadata !9, i32 0, i32 0} ; [ DW_TAG_auto_variable ] [m] [line 12]
!21 = metadata !{i32 786443, metadata !5, i32 11, i32 0, metadata !6, i32 0} ; [ DW_TAG_lexical_block ] [/home/qifcore/llvm-3.2/examples/QIF/CIF/text_example.c]
!22 = metadata !{i32 12, i32 0, metadata !21, null}
!23 = metadata !{i32 786688, metadata !21, metadata !"n", metadata !6, i32 12, metadata !9, i32 0, i32 0} ; [ DW_TAG_auto_variable ] [n] [line 12]
!24 = metadata !{i32 13, i32 0, metadata !21, null}
!25 = metadata !{i32 14, i32 0, metadata !21, null}
!26 = metadata !{i32 15, i32 0, metadata !21, null}
!27 = metadata !{i32 16, i32 0, metadata !28, null}
!28 = metadata !{i32 786443, metadata !21, i32 15, i32 0, metadata !6, i32 1} ; [ DW_TAG_lexical_block ] [/home/qifcore/llvm-3.2/examples/QIF/CIF/text_example.c]
!29 = metadata !{i32 17, i32 0, metadata !28, null}
!30 = metadata !{i32 18, i32 0, metadata !21, null}
!31 = metadata !{i32 20, i32 0, metadata !32, null}
!32 = metadata !{i32 786443, metadata !21, i32 19, i32 0, metadata !6, i32 2} ; [ DW_TAG_lexical_block ] [/home/qifcore/llvm-3.2/examples/QIF/CIF/text_example.c]
!33 = metadata !{i32 22, i32 0, metadata !34, null}
!34 = metadata !{i32 786443, metadata !32, i32 21, i32 0, metadata !6, i32 3} ; [ DW_TAG_lexical_block ] [/home/qifcore/llvm-3.2/examples/QIF/CIF/text_example.c]
!35 = metadata !{i32 23, i32 0, metadata !34, null}
!36 = metadata !{i32 25, i32 0, metadata !34, null}
!37 = metadata !{i32 26, i32 0, metadata !34, null}
!38 = metadata !{i32 27, i32 0, metadata !32, null}
!39 = metadata !{i32 28, i32 0, metadata !21, null}
!40 = metadata !{i32 786689, metadata !10, metadata !"a", metadata !6, i32 16777247, metadata !13, i32 0, i32 0} ; [ DW_TAG_arg_variable ] [a] [line 31]
!41 = metadata !{i32 31, i32 0, metadata !10, null}
!42 = metadata !{i32 786689, metadata !10, metadata !"a_len", metadata !6, i32 33554463, metadata !9, i32 0, i32 0} ; [ DW_TAG_arg_variable ] [a_len] [line 31]
!43 = metadata !{i32 786689, metadata !10, metadata !"c", metadata !6, i32 50331679, metadata !9, i32 0, i32 0} ; [ DW_TAG_arg_variable ] [c] [line 31]
!44 = metadata !{i32 786688, metadata !45, metadata !"gsum", metadata !6, i32 32, metadata !9, i32 0, i32 0} ; [ DW_TAG_auto_variable ] [gsum] [line 32]
!45 = metadata !{i32 786443, metadata !10, i32 31, i32 0, metadata !6, i32 4} ; [ DW_TAG_lexical_block ] [/home/qifcore/llvm-3.2/examples/QIF/CIF/text_example.c]
!46 = metadata !{i32 32, i32 0, metadata !45, null}
!47 = metadata !{i32 786688, metadata !45, metadata !"i", metadata !6, i32 32, metadata !9, i32 0, i32 0} ; [ DW_TAG_auto_variable ] [i] [line 32]
!48 = metadata !{i32 786688, metadata !45, metadata !"j", metadata !6, i32 32, metadata !9, i32 0, i32 0} ; [ DW_TAG_auto_variable ] [j] [line 32]
!49 = metadata !{i32 33, i32 0, metadata !45, null}
!50 = metadata !{i32 34, i32 0, metadata !51, null}
!51 = metadata !{i32 786443, metadata !45, i32 33, i32 0, metadata !6, i32 5} ; [ DW_TAG_lexical_block ] [/home/qifcore/llvm-3.2/examples/QIF/CIF/text_example.c]
!52 = metadata !{i32 35, i32 0, metadata !51, null}
!53 = metadata !{i32 36, i32 0, metadata !45, null}
!54 = metadata !{i32 37, i32 0, metadata !55, null}
!55 = metadata !{i32 786443, metadata !45, i32 36, i32 0, metadata !6, i32 6} ; [ DW_TAG_lexical_block ] [/home/qifcore/llvm-3.2/examples/QIF/CIF/text_example.c]
!56 = metadata !{i32 38, i32 0, metadata !55, null}
!57 = metadata !{i32 40, i32 0, metadata !58, null}
!58 = metadata !{i32 786443, metadata !45, i32 39, i32 0, metadata !6, i32 7} ; [ DW_TAG_lexical_block ] [/home/qifcore/llvm-3.2/examples/QIF/CIF/text_example.c]
!59 = metadata !{i32 41, i32 0, metadata !60, null}
!60 = metadata !{i32 786443, metadata !58, i32 41, i32 0, metadata !6, i32 8} ; [ DW_TAG_lexical_block ] [/home/qifcore/llvm-3.2/examples/QIF/CIF/text_example.c]
!61 = metadata !{i32 42, i32 0, metadata !62, null}
!62 = metadata !{i32 786443, metadata !60, i32 41, i32 0, metadata !6, i32 9} ; [ DW_TAG_lexical_block ] [/home/qifcore/llvm-3.2/examples/QIF/CIF/text_example.c]
!63 = metadata !{i32 43, i32 0, metadata !62, null}
!64 = metadata !{i32 45, i32 0, metadata !45, null}
!65 = metadata !{i32 46, i32 0, metadata !45, null}
!66 = metadata !{i32 47, i32 0, metadata !45, null}
