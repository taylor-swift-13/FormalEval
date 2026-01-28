Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

(* 正的偶数：存在 k>0 使 e = 2*k *)
Definition is_positive_even (e : Z) : Prop :=
  exists k : Z, e = 2 * k /\ (k > 0)%Z.

(* 任意整数 n 均可 *)
Definition problem_138_pre (n : Z) : Prop := True.

(* Spec：当且仅当存在四个正偶数之和等于 n 时返回 true *)
Definition problem_138_spec (n : Z) (b : bool) : Prop :=
  b = true <-> exists e1 e2 e3 e4 : Z,
    is_positive_even e1 /\
    is_positive_even e2 /\
    is_positive_even e3 /\
    is_positive_even e4 /\
    n = e1 + e2 + e3 + e4.

Example test_is_equal_to_sum_even_37 : problem_138_spec 37 false.
Proof.
  unfold problem_138_spec.
  split.
  - intro H. discriminate H.
  - intro H.
    destruct H as [e1 [e2 [e3 [e4 [H1 [H2 [H3 [H4 Hsum]]]]]]]].
    unfold is_positive_even in *.
    destruct H1 as [k1 [Hk1eq Hk1pos]].
    destruct H2 as [k2 [Hk2eq Hk2pos]].
    destruct H3 as [k3 [Hk3eq Hk3pos]].
    destruct H4 as [k4 [Hk4eq Hk4pos]].
    subst e1 e2 e3 e4.
    lia.
Qed.