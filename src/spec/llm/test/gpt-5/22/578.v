Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Inductive Any : Type :=
| AInt : Z -> Any
| AList : list Z -> Any.

Definition int := Z.

Definition IsInt (v : Any) (n : int) : Prop :=
  match v with
  | AInt m => m = n
  | AList _ => False
  end.

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

Example test_case_nested_lists: filter_integers_spec
  [AList []; AInt 1%Z; AList [3%Z; 8%Z; 4%Z]; AList []; AList [7%Z; 8%Z]; AInt 9%Z; AList [7%Z; 8%Z]]
  [1%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - intros n H. inversion H.
  - apply fir_cons_int with (n := 1%Z).
    + simpl. reflexivity.
    + apply fir_cons_nonint.
      * intros n H. inversion H.
      * apply fir_cons_nonint.
        { intros n H. inversion H. }
        { apply fir_cons_nonint.
          - intros n H. inversion H.
          - apply fir_cons_int with (n := 9%Z).
            + simpl. reflexivity.
            + apply fir_cons_nonint.
              * intros n H. inversion H.
              * apply fir_nil. }
Qed.