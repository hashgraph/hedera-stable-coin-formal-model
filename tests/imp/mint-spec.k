// The final total supply is the sum of all mints

// kompile --backend java imp.k
// kprove mint-spec.k


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
        test.mint(45); 
        // test.burn(30); // If you add this line back in, it will fail as expected
      => 
        .
    </k>
    <supply>
      0 => ?Mints:Int
    </supply>
    <mintsum>
      0 => ?Sum:Int
    </mintsum>
ensures ?Mints ==Int ?Sum

rule
    <k>
        Pgm:K 
      => 
        .
    </k>
    <supply>
      0 => ?FinalSupply:Int
    </supply>
    <mintsum>
      0 => ?Sum:Int
    </mintsum>
ensures ?Sum <=Int ?FinalSupply


endmodule