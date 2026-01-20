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

(* Parameters for the specific test case *)
Parameter test_dict : Dict.
Parameter key_p : Key.
Parameter key_b : Key.

(* String parameters for key names *)
Parameter str_p : string.
Parameter str_b : string.

(* Axioms describing the test case structure *)
Axiom test_keys : keys test_dict = [key_p; key_b].
Axiom key_p_str : KeyStr key_p str_p.
Axiom key_b_str : KeyStr key_b str_b.
Axiom p_is_lower : IsLower str_p.
Axiom b_is_lower : IsLower str_b.

Example check_dict_case_test : check_dict_case_spec test_dict true.
Proof.
  unfold check_dict_case_spec.
  split.
  - intros _.
    split.
    + rewrite test_keys. discriminate.
    + left.
      intros k Hk.
      rewrite test_keys in Hk.
      simpl in Hk.
      destruct Hk as [Hk | [Hk | Hk]].
      * subst k. exists str_p. split; [exact key_p_str | exact p_is_lower].
      * subst k. exists str_b. split; [exact key_b_str | exact b_is_lower].
      * contradiction.
  - intros _. reflexivity.
Qed.