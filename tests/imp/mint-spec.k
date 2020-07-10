// The final total supply is the sum of all mints

// kompile --backend java imp.k
// kprove mint-spec.k

requires "../../erc20.k"

module MINT-SPEC
  imports ERC20

rule
    <k>
        mint(Value)
      => 
        .
    ...</k>
    <supply>
      N => N +Int Value
    </supply>

endmodule