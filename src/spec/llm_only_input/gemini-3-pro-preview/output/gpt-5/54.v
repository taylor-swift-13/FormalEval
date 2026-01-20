Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Open Scope string_scope.

Fixpoint InStr (a : ascii) (s : string) : Prop :=
  match s with
  | EmptyString => False
  | String b s' => a = b \/ InStr a s'
  end.

Definition same_char_sets (s0 s1 : string) : Prop :=
  forall a : ascii, InStr a s0 <-> InStr a s1.

Definition same_chars_spec (s0 s1 : string) (res : bool) : Prop :=
  (res = true <-> same_char_sets s0 s1) /\
  (res = false <-> ~ same_char_sets s0 s1).

Example test_case_proof : same_chars_spec "eabcdzzzz" "dddzzzzzzzddeddabc" true.
Proof.
  (* Unfold the specification definition *)
  unfold same_chars_spec.
  
  (* We need to prove both parts of the conjunction *)
  split.
  
  - (* Part 1: true = true <-> same_char_sets ... *)
    split.
    + (* Left to Right: true = true -> same_char_sets ... *)
      intros _.
      unfold same_char_sets.
      intros a.
      split; intro H.
      
      * (* Forward: InStr a s0 -> InStr a s1 *)
        (* Simplify the hypothesis to expose the disjunction of characters *)
        simpl in H.
        (* Break down the hypothesis for every character in s0 *)
        repeat destruct H as [H | H].
        
        (* For each case, substitute 'a' and prove it exists in s1 *)
        (* Case 1: a = 'e' *)
        { subst. simpl. tauto. }
        (* Case 2: a = 'a' *)
        { subst. simpl. tauto. }
        (* Case 3: a = 'b' *)
        { subst. simpl. tauto. }
        (* Case 4: a = 'c' *)
        { subst. simpl. tauto. }
        (* Case 5: a = 'd' *)
        { subst. simpl. tauto. }
        (* Case 6: a = 'z' *)
        { subst. simpl. tauto. }
        (* Case 7: a = 'z' *)
        { subst. simpl. tauto. }
        (* Case 8: a = 'z' *)
        { subst. simpl. tauto. }
        (* Case 9: a = 'z' *)
        { subst. simpl. tauto. }
        (* Base case: False *)
        { contradiction. }

      * (* Backward: InStr a s1 -> InStr a s0 *)
        simpl in H.
        (* Break down the hypothesis for every character in s1 *)
        repeat destruct H as [H | H]; try contradiction; subst; simpl; tauto.
        
    + (* Right to Left: same_char_sets ... -> true = true *)
      intros _.
      reflexivity.

  - (* Part 2: true = false <-> ~ same_char_sets ... *)
    split.
    + (* true = false -> ... *)
      intros H.
      discriminate H.
    + (* ... -> true = false *)
      intros H.
      (* We proved same_char_sets holds in Part 1, so ~ same_char_sets is a contradiction *)
      (* However, we just need to show the implication holds. Since the RHS is false, 
         we can just prove the premise is false or rely on the fact that we don't strictly 
         need to prove the negation here if we just want to satisfy the logical equivalence 
         where the LHS is False. *)
      (* A simpler way: *)
      exfalso.
      apply H.
      unfold same_char_sets. intros a.
      split; intro HIn; simpl in HIn;
      repeat destruct HIn as [HIn | HIn]; try contradiction; subst; simpl; tauto.
Qed.