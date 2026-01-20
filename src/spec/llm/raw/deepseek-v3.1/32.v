
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Definition poly_spec (xs : list R) (x : R) (result : R) : Prop :=
  result = fold_left (fun acc '(i, coeff) => acc + coeff * (x ^ i)) (combine (seq 0 (length xs)) xs) 0.

Definition find_zero_spec (xs : list R) (x : R) : Prop :=
  exists dxs : list R,
    dxs = map (fun '(i, coeff) => coeff * INR i) (combine (seq 1 (length xs - 1)) (tl xs)) /\
    poly_spec xs x 0 /\
    (forall x' : R, poly_spec xs x' 0 -> x' = x) /\
    (length xs) mod 2 = 0 /\
    exists max_coeff : R,
      Forall (fun c => Rabs c <= Rabs max_coeff) xs /\
      max_coeff <> 0.
