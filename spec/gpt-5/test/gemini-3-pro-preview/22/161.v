Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Inductive Any : Type :=
| AnyInt : Z -> Any
| AnyStr : string -> Any
| AnyList : list Any -> Any.

Definition int := Z.

Definition IsInt (v : Any) (n : int) : Prop :=
  match v with
  | AnyInt z => n = z
  | _ => False
  end.

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

Example test_filter_integers_complex : 
  filter_integers_spec 
    [AnyInt 1%Z; AnyList [AnyInt 2%Z; AnyStr "3"]; AnyStr "4"; AnyList [AnyStr "5"; AnyInt 6%Z]; AnyInt 7%Z; AnyInt 7%Z] 
    [1%Z; 7%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1%Z).
  - simpl. reflexivity.
  - apply fir_cons_nonint.
    + intros n H. simpl in H. contradiction.
    + apply fir_cons_nonint.
      * intros n H. simpl in H. contradiction.
      * apply fir_cons_nonint.
        -- intros n H. simpl in H. contradiction.
        -- apply fir_cons_int with (n := 7%Z).
           ++ simpl. reflexivity.
           ++ apply fir_cons_int with (n := 7%Z).
              ** simpl. reflexivity.
              ** apply fir_nil.
Qed.