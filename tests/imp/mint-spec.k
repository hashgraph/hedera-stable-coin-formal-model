// The final total supply is the sum of all mints

// kompile --backend java imp.k
// kprove mint-spec.k


module MINT-SPEC
  imports IMP
 
rule
    <k>
        test.mint(45); 
      => 
        .
    </k>
    <supply>
      0 => ?FinalSupply:Int
    </supply>
    <mintsum>
      0 => ?Sum:Int
    </mintsum>
ensures ?FinalSupply ==Int ?Sum

rule
    <k>
        mint(Value)
      => 
        .
    ...</k>
    <supply>
      N => N +Int Value
    </supply>
    <mintsum>
      M => M +Int Value
    </mintsum>

endmodule