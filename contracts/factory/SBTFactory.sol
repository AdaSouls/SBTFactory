// SPDX-License-Identifier: MIT
pragma solidity ^0.8.8;

import "../tokens/ERC5192.sol";

contract SBTFactory {
  ERC5192[] public ERC5192Array;

  function CreateERC5192(string memory _tokenName, string memory _tokenSymbol, bool _owner) public returns (address) {
    require(bytes(_tokenName).length != 0, "SBTFactory: token name is empty");
    require(bytes(_tokenName).length != 0, "SBTFactory: token symbol is empty");
    require(address(msg.sender) != address(0), "SBTFactory: sender is ZERO_ADDRESS");
    ERC5192 sbt = new ERC5192(_tokenName, _tokenSymbol, _owner);
    ERC5192Array.push(sbt);
    return address(sbt);
  }

}