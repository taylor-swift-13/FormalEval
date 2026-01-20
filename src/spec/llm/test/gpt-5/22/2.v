Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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

Parameters VInt4 VEmptyBrace VEmptyList VReal232 VInt9 VStringADASD : Any.
Axiom IsInt_VInt4 : IsInt VInt4 4%Z.
Axiom IsInt_VInt9 : IsInt VInt9 9%Z.
Axiom NotInt_VEmptyBrace : forall n, ~ IsInt VEmptyBrace n.
Axiom NotInt_VEmptyList : forall n, ~ IsInt VEmptyList n.
Axiom NotInt_VReal232 : forall n, ~ IsInt VReal232 n.
Axiom NotInt_VStringADASD : forall n, ~ IsInt VStringADASD n.

Example test_case_mixed: filter_integers_spec [VInt4; VEmptyBrace; VEmptyList; VReal232; VInt9; VStringADASD] [4%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - exact IsInt_VInt4.
  - eapply fir_cons_nonint.
    + exact NotInt_VEmptyBrace.
    + eapply fir_cons_nonint.
      * exact NotInt_VEmptyList.
      * eapply fir_cons_nonint.
        -- exact NotInt_VReal232.
        -- eapply fir_cons_int.
           ++ exact IsInt_VInt9.
           ++ eapply fir_cons_nonint.
              ** exact NotInt_VStringADASD.
              ** apply fir_nil.
Qed.