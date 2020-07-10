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

endmodule 