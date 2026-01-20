Require Import Coq.Strings.String Coq.Strings.Ascii Coq.ZArith.ZArith.
Open Scope Z_scope.

(* 基础：字符串相等判定 *)
Fixpoint string_eqb (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 t1, String c2 t2 => if Ascii.eqb c1 c2 then string_eqb t1 t2 else false
  | _, _ => false
  end.

(* 删除前缀 p，匹配成功返回剩余串 *)
Fixpoint drop_prefix (p s : string) : option string :=
  match p, s with
  | EmptyString, _ => Some s
  | String c1 p', String c2 s' => if Ascii.eqb c1 c2 then drop_prefix p' s' else None
  | _, _ => None
  end.

(* 数字字符与取值 *)
Definition is_digit (c : ascii) : bool :=
  match c with
  | "0"%char | "1"%char | "2"%char | "3"%char | "4"%char
  | "5"%char | "6"%char | "7"%char | "8"%char | "9"%char => true
  | _ => false
  end.

Definition digit_val (c : ascii) : Z :=
  match c with
  | "0"%char => 0 | "1"%char => 1 | "2"%char => 2 | "3"%char => 3 | "4"%char => 4
  | "5"%char => 5 | "6"%char => 6 | "7"%char => 7 | "8"%char => 8 | "9"%char => 9
  | _ => 0
  end.

(* 读取十进制非负整数 *)
Fixpoint read_number_acc (s : string) (acc : Z) (seen : bool) : option (Z * string) :=
  match s with
  | EmptyString => if seen then Some (acc, EmptyString) else None
  | String c rest =>
      if is_digit c then
        read_number_acc rest (10 * acc + digit_val c) true
      else if seen then Some (acc, s) else None
  end.

Definition read_number (s : string) : option (Z * string) := read_number_acc s 0 false.

(* 解析 "x apples and y oranges" *)
Definition parse_apples_oranges (s : string) : option (Z * Z) :=
  match read_number s with
  | None => None
  | Some (a, s1) =>
      match drop_prefix " apples and "%string s1 with
      | None => None
      | Some s2 =>
          match read_number s2 with
          | None => None
          | Some (o, s3) =>
              match drop_prefix " oranges"%string s3 with
              | Some rest => Some (a, o) (* 允许末尾为空或忽略多余内容 *)
              | None => None
              end
          end
      end
  end.

Definition fruit_distribution_impl (s : string) (n : Z) : Z :=
  match parse_apples_oranges s with
  | Some (apples, oranges) => n - (apples + oranges)
  | None => n (* 解析失败时不做更改 *)
  end.

(* 测试用例 *)
Example fruit_distribution_impl_ex1:
  fruit_distribution_impl "5 apples and 6 oranges"%string 19%Z = 8%Z.
Proof. reflexivity. Qed.

Example fruit_distribution_impl_ex2:
  fruit_distribution_impl "0 apples and 1 oranges"%string 3%Z = 2%Z.
Proof. reflexivity. Qed.

Definition fruit_distribution_spec (s : string) (n : Z) (output : Z) : Prop :=
  output = fruit_distribution_impl s n.


