Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Parameter Dict : Type.
Parameter Key : Type.
Parameter keys : Dict -> list Key.
Parameter KeyStr : Key -> string -> Prop.
Parameter IsLower : string -> Prop.
Parameter IsUpper : string -> Prop.

Definition check_dict_case_spec (d : Dict) (res : bool) : Prop :=
  res = true <->
  keys d <> nil /\
  ( (forall k, In k (keys d) -> exists s, KeyStr k s /\ IsLower s) \/
    (forall k, In k (keys d) -> exists s, KeyStr k s /\ IsUpper s) ).

Section Test_Case_Proof.
  (* 
     Test case configuration:
     input = [{'p': 'pineapple', 'b': 'banana'}], output = true 
     
     Since Dict, Key, etc. are abstract Parameters, we introduce variables
     and hypotheses to represent the specific structure of the test case.
  *)

  Variable d : Dict.
  Variable k_p k_b : Key.
  Variable s_pineapple s_banana : string.

  (* Hypothesis: The dictionary contains exactly two keys *)
  Hypothesis H_keys : keys d = [k_p; k_b].

  (* Hypothesis: The mappings correspond to the test case *)
  Hypothesis H_map_p : KeyStr k_p s_pineapple.
  Hypothesis H_map_b : KeyStr k_b s_banana.

  (* Hypothesis: The strings are lowercase *)
  Hypothesis H_low_p : IsLower s_pineapple.
  Hypothesis H_low_b : IsLower s_banana.

  Example test_check_dict_case : check_dict_case_spec d true.
  Proof.
    unfold check_dict_case_spec.
    split.
    - (* Direction: true = true -> Specification Holds *)
      intros _.
      split.
      + (* Part 1: keys d <> nil *)
        rewrite H_keys.
        intro H_nil.
        discriminate H_nil.
      + (* Part 2: All Lower or All Upper *)
        (* Since our test case is all lower, we prove the left disjunct *)
        left.
        intros k H_in.
        rewrite H_keys in H_in.
        simpl in H_in.
        destruct H_in as [H_is_p | [H_is_b | H_false]].
        * (* Case: k is 'p' *)
          subst k.
          exists s_pineapple.
          split.
          -- apply H_map_p.
          -- apply H_low_p.
        * (* Case: k is 'b' *)
          subst k.
          exists s_banana.
          split.
          -- apply H_map_b.
          -- apply H_low_b.
        * (* Case: End of list *)
          contradiction H_false.
    - (* Direction: Specification Holds -> true = true *)
      intros _.
      reflexivity.
  Qed.

End Test_Case_Proof.