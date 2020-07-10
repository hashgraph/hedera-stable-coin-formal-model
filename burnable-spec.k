// The final total supply is the sum of all mints

// kompile --backend java erc20.k
// kprove mint-spec.k

requires "erc20.k"

module BURNABLE-SPEC
  imports ERC20

rule
    <k>
        burn(Value, {caller: Owner})
      => 
        .
    ...</k>
    <supply>
      N => N -Int Value
    </supply>
    <tokenOwner> Owner </tokenOwner>


endmodule