requires "erc20.k"

module CONSTRUCTOR-SPEC
  imports ERC20

rule
    <k>
        constructor(TokenNameArg, TokenSymbolArg, TokenDecimalArg, TotalSupplyArg, SupplyManagerArg, AssetProtectionManagerArg, { caller : Caller } )
      => 
        .
    ...</k>
    <tokenName> _TokenName => TokenNameArg </tokenName>
    <tokenSymbol> _TokenSymbol => TokenSymbolArg </tokenSymbol>
    <tokenDecimal> _TokenDecimal => TokenDecimalArg </tokenDecimal>
    <totalSupply> _TotalSupply => TotalSupplyArg </totalSupply>
    <tokenOwner> TokenOwner => Caller </tokenOwner>
    <supplyManager> _SupplyManager => SupplyManagerArg </supplyManager>
    <assetProtectionManager> _AssetProtectionManager => AssetProtectionManagerArg </assetProtectionManager>
requires TokenOwner ==Int 0
    andBool TokenDecimalArg >=Int 0
    andBool TotalSupplyArg >=Int 0
    andBool Caller =/=Int 0
    andBool SupplyManagerArg =/=Int 0
    andBool AssetProtectionManagerArg =/=Int 0

// if the TokenOwner has already been set, the constructor should throw
rule
    <k>
        constructor(_:Int, _:Int, _:Int, _:Int, _:Int, _:Int, { caller : Caller } )
      =>
        throw
    ...</k>
    <tokenOwner> TokenOwner </tokenOwner>
requires TokenOwner =/=Int 0
    andBool Caller =/=Int 0

// if the constructor is called twice in a row, the resulting state will only reflect the first call
rule
    <k>
        constructor(TokenNameArg, TokenSymbolArg, TokenDecimalArg, TotalSupplyArg, SupplyManagerArg, AssetProtectionManagerArg, { caller : Caller } )
        ~>
        constructor(_:Int, _:Int, _:Int, _:Int, _:Int, _:Int, { caller : _:Int } )
      =>
         throw
    ...</k>
    <tokenName> _TokenName => TokenNameArg </tokenName>
    <tokenSymbol> _TokenSymbol => TokenSymbolArg </tokenSymbol>
    <tokenDecimal> _TokenDecimal => TokenDecimalArg </tokenDecimal>
    <totalSupply> _TotalSupply => TotalSupplyArg </totalSupply>
    <tokenOwner> TokenOwner => Caller </tokenOwner>
    <supplyManager> _SupplyManager => SupplyManagerArg </supplyManager>
    <assetProtectionManager> _AssetProtectionManager => AssetProtectionManagerArg </assetProtectionManager>
requires TokenOwner ==Int 0
    andBool TokenDecimalArg >=Int 0
    andBool TotalSupplyArg >=Int 0
    andBool Caller =/=Int 0
    andBool SupplyManagerArg =/=Int 0
    andBool AssetProtectionManagerArg =/=Int 0

endmodule