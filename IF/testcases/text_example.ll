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
  store i32 %c, i32* %c.addr, align 4
  %0 = load i32* %a_i.addr, align 4
  %call = call i32 @abs(i32 %0) nounwind readnone
  store i32 %call, i32* %m, align 4
  %1 = load i32* %c.addr, align 4
  %call1 = call i32 @abs(i32 %1) nounwind readnone
  store i32 %call1, i32* %n, align 4
  %2 = load i32* %m, align 4
  %cmp = icmp eq i32 %2, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  store i32 1073741823, i32* %m, align 4
  br label %if.end10

if.else:                                          ; preds = %entry
  %3 = load i32* %n, align 4
  %cmp2 = icmp ne i32 %3, 0
  br i1 %cmp2, label %if.then3, label %if.end9

if.then3:                                         ; preds = %if.else
  br label %while.cond

while.cond:                                       ; preds = %if.end, %if.then3
  %4 = load i32* %m, align 4
  %5 = load i32* %n, align 4
  %cmp4 = icmp ne i32 %4, %5
  br i1 %cmp4, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %6 = load i32* %m, align 4
  %7 = load i32* %n, align 4
  %cmp5 = icmp sgt i32 %6, %7
  br i1 %cmp5, label %if.then6, label %if.else7

if.then6:                                         ; preds = %while.body
  %8 = load i32* %m, align 4
  %9 = load i32* %n, align 4
  %sub = sub nsw i32 %8, %9
  store i32 %sub, i32* %m, align 4
  br label %if.end

if.else7:                                         ; preds = %while.body
  %10 = load i32* %n, align 4
  %11 = load i32* %m, align 4
  %sub8 = sub nsw i32 %10, %11
  store i32 %sub8, i32* %n, align 4
  br label %if.end

if.end:                                           ; preds = %if.else7, %if.then6
  br label %while.cond

while.end:                                        ; preds = %while.cond
  br label %if.end9

if.end9:                                          ; preds = %while.end, %if.else
  br label %if.end10

if.end10:                                         ; preds = %if.end9, %if.then
  %12 = load i32* %m, align 4
  ret i32 %12
}

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
  store i32 %a_len, i32* %a_len.addr, align 4
  store i32 %c, i32* %c.addr, align 4
  %0 = load i32** %a.addr, align 4
  %tobool = icmp ne i32* %0, null
  br i1 %tobool, label %lor.lhs.false, label %if.then

lor.lhs.false:                                    ; preds = %entry
  %1 = load i32* %a_len.addr, align 4
  %cmp = icmp eq i32 %1, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %lor.lhs.false, %entry
  %2 = load i32* %c.addr, align 4
  store i32 %2, i32* %gsum, align 4
  br label %if.end7

if.else:                                          ; preds = %lor.lhs.false
  %3 = load i32** %a.addr, align 4
  %arrayidx = getelementptr inbounds i32* %3, i32 0
  %4 = load i32* %arrayidx, align 4
  %cmp1 = icmp eq i32 %4, 0
  br i1 %cmp1, label %land.lhs.true, label %if.else4

land.lhs.true:                                    ; preds = %if.else
  %5 = load i32* %c.addr, align 4
  %cmp2 = icmp eq i32 %5, 0
  br i1 %cmp2, label %if.then3, label %if.else4

if.then3:                                         ; preds = %land.lhs.true
  store i32 1073741823, i32* %gsum, align 4
  br label %if.end

if.else4:                                         ; preds = %land.lhs.true, %if.else
  store i32 0, i32* %gsum, align 4
  store i32 0, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.else4
  %6 = load i32* %i, align 4
  %7 = load i32* %a_len.addr, align 4
  %cmp5 = icmp slt i32 %6, %7
  br i1 %cmp5, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %8 = load i32* %gsum, align 4
  %9 = load i32* %i, align 4
  %10 = load i32** %a.addr, align 4
  %arrayidx6 = getelementptr inbounds i32* %10, i32 %9
  %11 = load i32* %arrayidx6, align 4
  %12 = load i32* %c.addr, align 4
  %call = call i32 @gcd(i32 %11, i32 %12)
  %add = add nsw i32 %8, %call
  store i32 %add, i32* %gsum, align 4
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %13 = load i32* %i, align 4
  %inc = add nsw i32 %13, 1
  store i32 %inc, i32* %i, align 4
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %if.end

if.end:                                           ; preds = %for.end, %if.then3
  br label %if.end7

if.end7:                                          ; preds = %if.end, %if.then
  %14 = load i32* %c.addr, align 4
  %rem = srem i32 %14, 10
  store i32 %rem, i32* %j, align 4
  %15 = load i32* %gsum, align 4
  %16 = load i32* %c.addr, align 4
  %div = sdiv i32 %15, %16
  %17 = load i32* %j, align 4
  %18 = load i32** @out, align 4
  %arrayidx8 = getelementptr inbounds i32* %18, i32 %17
  store i32 %div, i32* %arrayidx8, align 4
  %19 = load i32* %gsum, align 4
  ret i32 %19
}
