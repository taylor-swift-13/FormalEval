
Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists (n : Z), n ^ 3 = Z.abs a.
