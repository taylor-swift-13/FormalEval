(* 引用 Coq 的标准库，用于字符串、列表和实数 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.

(* 导入列表的常用写法，例如 [a;b;c] *)
Import ListNotations.

(* 开放实数的作用域，以便使用 <, <=, = 等符号 *)
Open Scope R_scope.
Open Scope string_scope.

(*
 * @name grade_relation
 * @description 这个关系描述了单个 GPA 值 (gpa) 与其对应的
 *              单个字母等级 (grade) 之间的逻辑。
 *              它使用了析取（逻辑或 \/）来连接所有可能的评分规则。
 * @param gpa : R        一个实数，代表输入的 GPA。
 * @param grade : string 一个字符串，代表输出的字母等级。
 *)
Definition grade_relation (gpa : R) (grade : string) : Prop :=
  (gpa = 4.0 /\ grade = "A+") \/
  (3.7 < gpa /\ gpa < 4.0 /\ grade = "A") \/
  (3.3 < gpa /\ gpa <= 3.7 /\ grade = "A-") \/
  (3.0 < gpa /\ gpa <= 3.3 /\ grade = "B+") \/
  (2.7 < gpa /\ gpa <= 3.0 /\ grade = "B") \/
  (2.3 < gpa /\ gpa <= 2.7 /\ grade = "B-") \/
  (2.0 < gpa /\ gpa <= 2.3 /\ grade = "C+") \/
  (1.7 < gpa /\ gpa <= 2.0 /\ grade = "C") \/
  (1.3 < gpa /\ gpa <= 1.7 /\ grade = "C-") \/
  (1.0 < gpa /\ gpa <= 1.3 /\ grade = "D+") \/
  (0.7 < gpa /\ gpa <= 1.0 /\ grade = "D") \/
  (0.0 < gpa /\ gpa <= 0.7 /\ grade = "D-") \/
  (gpa = 0.0 /\ grade = "E").

Definition problem_81_pre (gpas : list R) : Prop :=
  Forall (fun g => 0 <= g /\ g <= 4) gpas.

(*
 * @name numerical_letter_grade_spec
 * @description 这是 `numerical_letter_grade` 函数的完整规约.
 *              它规定了输入列表 (gpas) 和输出列表 (grades) 之间的关系。
 *
 *              `Forall2` 是一个高阶谓词，它断言两个列表的长度相同，
 *              并且对于两个列表中所有位置对应的元素对，`grade_relation` 关系都成立。
 *
 * @param gpas : list R          代表输入的 GPA 列表。
 * @param grades : list string   代表输出的字母等级列表。
 *)
Definition problem_81_spec (gpas : list R) (grades : list string) : Prop :=
  Forall2 grade_relation gpas grades.

(* 
   Helper tactic to solve linear real inequalities involved in the grading scheme.
   This avoids using Lra/Micromega which might be missing in some environments,
   and manually proves the inequalities by scaling by 10 and comparing integers.
   It also replaces the deprecated IZR_neq with eq_IZR_contrapositive.
*)
Ltac solve_grade_ineq :=
  try apply Rle_refl; (* Handle cases like 3 <= 3 *)
  match goal with
  | [ |- ?a < ?b ] =>
      apply Rmult_lt_reg_r with (r := 10);
      [ apply IZR_lt; reflexivity | ]; (* Prove 0 < 10 *)
      unfold Rdiv;
      try rewrite Rmult_assoc;
      try rewrite Rinv_l by (apply eq_IZR_contrapositive; discriminate); (* Prove 10 <> 0 *)
      try rewrite Rmult_1_r;
      try rewrite <- mult_IZR; (* Combine IZR a * IZR b *)
      apply IZR_lt; vm_compute; reflexivity (* Solve Z inequality *)
  | [ |- ?a <= ?b ] =>
      apply Rmult_le_reg_r with (r := 10);
      [ apply IZR_lt; reflexivity | ];
      unfold Rdiv;
      try rewrite Rmult_assoc;
      try rewrite Rinv_l by (apply eq_IZR_contrapositive; discriminate);
      try rewrite Rmult_1_r;
      try rewrite <- mult_IZR;
      apply IZR_le; vm_compute; reflexivity
  end.

(* 
   Tactic to attempt to solve the current branch of grade_relation.
   It uses 'solve' to ensure it either fully succeeds (solving all subgoals)
   or fails immediately, triggering the backtracking mechanism in 'first'.
*)
Ltac solve_branch :=
  solve [
    split; [ 
      (* Handle the numeric condition part *)
      try split; (* Separate lower and upper bounds if present *)
      try reflexivity; (* Handle gpa = 4.0 *)
      try solve_grade_ineq (* Handle inequalities *)
    | 
      (* Handle the string grade part *)
      reflexivity 
    ]
  ].

(* 
   Example Proof 
   Input: [4.0; 3; 1.7; 2; 3.5]
   Output: ["A+"; "B"; "C-"; "C"; "A-"]
*)
Example test_numerical_letter_grade :
  problem_81_spec 
    [4.0; IZR 3; 1.7; IZR 2; 3.5] 
    ["A+"; "B"; "C-"; "C"; "A-"].
Proof.
  unfold problem_81_spec.
  repeat constructor.
  all: unfold grade_relation.
  
  (* 
     Automated proof search for the correct grade branch.
     The loop tries to prove the current branch (left) using solve_branch.
     If solve_branch fails (e.g., wrong inequality), it moves to the next branch (right).
  *)
  all: repeat (first [ left; solve_branch | right ]).
  
  (* 
     Handle the final case if the loop pushed to the very end.
     This is necessary because the last branch is not followed by 'right'.
  *)
  all: try solve_branch.
Qed.