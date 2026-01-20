Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter mkInt : Z -> Any.
Parameter mkList : list Any -> Any.
Axiom IsInt_mkInt : forall z, IsInt (mkInt z) z.
Axiom not_IsInt_mkList : forall l n, ~ IsInt (mkList l) n.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Example test_case_new: filter_integers_spec
  [mkList []; mkList []; mkInt 8%Z; mkList [mkInt 5%Z];
   mkList [mkInt 8%Z; mkInt 7%Z; mkInt 8%Z];
   mkList [mkInt 8%Z; mkInt 7%Z; mkInt 8%Z];
   mkInt 9%Z; mkInt 9%Z; mkList []]
  [8%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. intros n. apply (not_IsInt_mkList []).
  apply fir_cons_nonint. intros n. apply (not_IsInt_mkList []).
  apply fir_cons_int. apply IsInt_mkInt.
  apply fir_cons_nonint. intros n. apply (not_IsInt_mkList [mkInt 5%Z]).
  apply fir_cons_nonint. intros n. apply (not_IsInt_mkList [mkInt 8%Z; mkInt 7%Z; mkInt 8%Z]).
  apply fir_cons_nonint. intros n. apply (not_IsInt_mkList [mkInt 8%Z; mkInt 7%Z; mkInt 8%Z]).
  apply fir_cons_int. apply IsInt_mkInt.
  apply fir_cons_int. apply IsInt_mkInt.
  apply fir_cons_nonint. intros n. apply (not_IsInt_mkList []).
  constructor.
Qed.