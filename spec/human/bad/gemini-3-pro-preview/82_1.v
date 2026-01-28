Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_82_pre (s : string) : Prop := True.

Definition  problem_82_spec (s : string) (b : bool) : Prop :=
  b = true <-> prime (Z.of_nat (length s)).

Example test_problem_82 : problem_82_spec "Hello" true.
Proof.
  unfold problem_82_spec.
  simpl.
  split.
  - intros _.
    apply prime_intro.
    + (* Prove 1 < 5 *)
      compute. reflexivity.
    + (* Prove forall n, 1 <= n < 5 -> rel_prime n 5 *)
      intros n [Hge Hlt].
      (* We manually enumerate the possible values of n (1, 2, 3, 4) 
         since we avoid using external solvers like Lia/Omega which might fail to load. *)
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4).
      {
        destruct n; try (simpl in Hge; inversion Hge).
        destruct p.
        - (* n is xI p (odd) *)
          destruct p.
          + (* n = 4p+3 *)
            destruct p; simpl in Hlt; discriminate.
          + (* n = 4p+1 *)
            (* If p=1, n=5, not < 5. If p>1, n>5. *)
            destruct p; simpl in Hlt; discriminate.
          + (* n = 3 *)
            right; right; left; reflexivity.
        - (* n is xO p (even) *)
          destruct p.
          + (* n = 4p+2 *)
            destruct p; simpl in Hlt; discriminate.
          + (* n = 4p *)
            destruct p.
            * simpl in Hlt; discriminate.
            * simpl in Hlt; discriminate.
            * (* n = 4 *)
              right; right; right; reflexivity.
          + (* n = 2 *)
            right; left; reflexivity.
        - (* n = 1 *)
          left; reflexivity.
      }
      destruct H_cases as [-> | [-> | [-> | ->]]];
        apply Zgcd_1_rel_prime; compute; reflexivity.
  - intros _. reflexivity.
Qed.