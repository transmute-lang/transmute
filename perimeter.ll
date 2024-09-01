; ModuleID = 'main'
source_filename = "main"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%"Square#id1" = type { %"Point#id0", %"Point#id0" }
%"Point#id0" = type { i64, i64 }

declare void @print(i64)

define i64 @f(i64 %"n#param#sym25#") {
entry:
  %"square#local#sym26#" = alloca %"Square#id1", align 8
  store i64 0, ptr %"square#local#sym26#", align 4
  %"square#local#sym26#.repack13" = getelementptr inbounds %"Point#id0", ptr %"square#local#sym26#", i64 0, i32 1
  store i64 0, ptr %"square#local#sym26#.repack13", align 4
  %"square#local#sym26#.repack11" = getelementptr inbounds %"Square#id1", ptr %"square#local#sym26#", i64 0, i32 1
  store i64 %"n#param#sym25#", ptr %"square#local#sym26#.repack11", align 4
  %"square#local#sym26#.repack11.repack14" = getelementptr inbounds %"Square#id1", ptr %"square#local#sym26#", i64 0, i32 1, i32 1
  store i64 %"n#param#sym25#", ptr %"square#local#sym26#.repack11.repack14", align 4
  %factor = mul i64 %"n#param#sym25#", 2
  %"add#" = shl i64 %factor, 1
  ret i64 %"add#"
}
