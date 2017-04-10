= (fix mul (n m : Datatypes.nat) {struct n} : Datatypes.nat :=
          match n with
          | 0 => 0
          | Datatypes.S p =>
              (fix add (n0 m0 : Datatypes.nat) {struct n0} :
                 Datatypes.nat :=
                 match n0 with
                 | 0 => m0
                 | Datatypes.S p0 => Datatypes.S (add p0 m0)
                 end) m (mul p m)
          end) m 0
     : Datatypes.nat
