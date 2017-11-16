open preamble astBakeryTheory (* todo: shouldn't have to depend on astBakery *)

val _ = new_theory "endpointLang";

val _ = Datatype`
endpoint = Nil
         | Send proc varN endpoint
         | Receive proc varN endpoint
         | IntChoice bool proc endpoint
         | ExtChoice proc endpoint endpoint
         | IfThen varN endpoint endpoint
         | Let varN (datum list -> datum) (varN list) endpoint`
               
val _ = export_theory ()
