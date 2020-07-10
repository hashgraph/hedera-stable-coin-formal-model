// The final total supply is the sum of all mints

module MINT-SPEC
  imports IMP
/*
rule
    <k>
      mint(Value)
    =>
      .K
    ...</k>
    <mintsum> N:Int => (N +Int Value) </mintsum>
*/

rule
    <k>
        mint(2); burn(1); 
      => 
        .
    </k>
    <supply>
      0 => ?Mints:Int
    </supply>
    <mintsum>
      0 => ?Sum:Int
    </mintsum>
ensures ?Mints =/=Int ?Sum



endmodule