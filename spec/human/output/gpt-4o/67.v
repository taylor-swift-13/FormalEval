(* 引入Coq自带的库，用于处理整数（Z）和字符串（string） *)
Require Import ZArith Strings.String.
Require Import Coq.Strings.Ascii.

Open Scope string_scope.
Open Scope Z_scope.

(* 将字符转换为数字的辅助函数 *)
Definition char_to_digit (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - nat_of_ascii "0"%char).

(* 辅助函数：将字符串转换为整数 *)
Fixpoint string_to_Z_aux (s : string) (acc : Z) : Z :=
  match s with
  | EmptyString => acc
  | String c s' => string_to_Z_aux s' (acc * 10 + char_to_digit c)
  end.

(* 主函数：将字符串转换为整数 *)
Definition string_to_Z (s : string) : Z :=
  string_to_Z_aux s 0.

(* 辅助规约: parse_fruit_string
   这个规约描述了从输入字符串 s 中解析出苹果和橘子数量的逻辑。 *)
Definition parse_fruit_string (s : string) (apples oranges : Z) : Prop :=
  exists s_apples s_oranges,
    apples = string_to_Z s_apples /\
    oranges = string_to_Z s_oranges /\
    s = (s_apples ++ " apples and " ++ s_oranges ++ " oranges")%string.

Definition problem_67_pre (s : string) (n : Z) : Prop := True.

Definition problem_67_spec (s : string) (n : Z) (ret : Z) : Prop :=
  exists apples oranges,
    parse_fruit_string s apples oranges /\
    ret = n - (apples + oranges).

(* 证明示例 *)
Example example_proof :
  problem_67_spec "5 apples and 6 oranges" 19 8.
Proof.
  unfold problem_67_spec.
  exists 5, 6.
  split.
  - unfold parse_fruit_string.
    exists "5", "6".
    split; [reflexivity|].
    split; [reflexivity|].
    reflexivity.
  - simpl. compute. reflexivity.
Qed.