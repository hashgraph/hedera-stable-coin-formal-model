// The final total supply is the sum of all mints

// kompile --backend java erc20.k
// kprove mint-spec.k

requires "erc20.k"

module MINTABLE-SPEC
  imports ERC20

rule
    <k>
        mint(Value)
      => 
        .
    ...</k>
    <totalSupply>
      N => N +Int Value
    </totalSupply>
    

endmodule