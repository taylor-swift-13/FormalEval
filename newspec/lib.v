(* 1. 导入 Coq 标准库中处理字符串、ASCII 字符和列表所需的部分 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations. (* 允许使用 [a; b; c] 这样的列表表示法 *)

(* 开启字符串作用域，这样我们就可以直接写 "Hello" 来表示一个字符串 *)
Open Scope string_scope.

(* 2. 定义从 string 到 list ascii 的转换函数 *)
(*    这个函数递归地遍历字符串：
      - 如果是空字符串 (EmptyString)，返回空列表 (nil)。
      - 如果是字符 c 后面跟着字符串 s' (String c s')，
        则将 c 添加到对 s' 递归调用的结果列表的前面 (c :: ...)。
*)
Fixpoint string_to_list_ascii (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s' => c :: (string_to_list_ascii s')
  end.

(* 3. 定义一个我们将要转换的示例字符串 *)
Definition my_string : string := "Coq Example!".

(* 4. 调用函数，将 my_string 转换为一个 ASCII 列表 *)
Definition my_list_ascii : list ascii := string_to_list_ascii my_string.

(* 5. 使用 Compute 命令来查看转换后的结果 *)
(*    Compute 会计算一个表达式并打印出它的范式（最终结果）。*)
Compute my_list_ascii.