Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

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

Parameter from_reals : list R -> Any.
Axiom NotInt_from_reals : forall rs n, ~ IsInt (from_reals rs) n.

Example test_case_reals_list: filter_integers_spec [from_reals [2.7%R; 3.0%R; 1.9007953338604962%R; 1.8262900227722207%R; 1.5%R; 1.5%R]] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - intros n. exact (NotInt_from_reals [2.7%R; 3.0%R; 1.9007953338604962%R; 1.8262900227722207%R; 1.5%R; 1.5%R] n).
  - constructor.
Qed.