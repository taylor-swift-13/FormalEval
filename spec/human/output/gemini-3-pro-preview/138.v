Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

(* Definition from specification *)
Definition is_positive_even (e : Z) : Prop :=
  exists k : Z, e = 2 * k /\ (k > 0)%Z.

Definition problem_138_pre (n : Z) : Prop := True.

Definition problem_138_spec (n : Z) (b : bool) : Prop :=
  b = true <-> exists e1 e2 e3 e4 : Z,
    is_positive_even e1 /\
    is_positive_even e2 /\
    is_positive_even e3 /\
    is_positive_even e4 /\
    n = e1 + e2 + e3 + e4.

(* Test case proof *)
Example test_case_1 : problem_138_spec 4 false.
Proof.
  unfold problem_138_spec.
  split.
  - (* Direction: false = true -> exists ... *)
    intro H.
    discriminate H.
  - (* Direction: exists ... -> false = true *)
    intros [e1 [e2 [e3 [e4 [H1 [H2 [H3 [H4 Hsum]]]]]]]].
    (* Unfold definitions to expose the underlying integers *)
    unfold is_positive_even in *.
    destruct H1 as [k1 [He1 Hk1]].
    destruct H2 as [k2 [He2 Hk2]].
    destruct H3 as [k3 [He3 Hk3]].
    destruct H4 as [k4 [He4 Hk4]].
    (* Substitute the definitions of even numbers into the sum *)
    subst.
    (* Use Linear Integer Arithmetic solver to show contradiction:
       Since k_i > 0, k_i >= 1.
       Therefore 2*k_i >= 2.
       Sum >= 2+2+2+2 = 8.
       But sum is 4. 4 >= 8 is False. *)
    lia.
Qed.