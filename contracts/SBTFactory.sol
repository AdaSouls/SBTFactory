// SPDX-License-Identifier: MIT
pragma solidity ^0.8.8;

import "./SBT.sol";

contract SBTFactory {
  SBT[] public sbtArray;
  mapping(address => address[]) public tokensByOwner;

  function CreateNewSBT(string memory _name, string memory _symbol) public returns (address) {
    require(bytes(_name).length != 0, "SBTFactory: token name is empty");
    require(bytes(_symbol).length != 0, "SBTFactory: token symbol is empty");
    require(address(msg.sender) != address(0), "SBTFactory: sender is ZERO_ADDRESS");
    SBT sbt = new SBT(_name, _symbol);
    sbtArray.push(sbt);
    tokensByOwner[msg.sender].push(address(sbt));
    return address(sbt);
  }

  function sbtIssuerWithIndex(uint256 _sbtIndex, address _beneficiary, string calldata _uri) public {
    require(address(msg.sender) != address(0), "SBTFactory: sender is ZERO_ADDRESS");
    require(address(_beneficiary) != address(0), "SBTFactory: beneficiary is ZERO_ADDRESS");
    SBT(address(sbtArray[_sbtIndex])).issue(_beneficiary, _uri);
  }

  function sbtBurnerWithIndex(uint256 _sbtIndex, uint256 _tokenId) public {
    require(address(msg.sender) != address(0), "SBTFactory: sender is ZERO_ADDRESS");
    return SBT(address(sbtArray[_sbtIndex])).burn(_tokenId);
  }

  function sbtIssuerWithAddress(address _sbtAddress, address _beneficiary, string calldata _uri) public {
    require(address(msg.sender) != address(0), "SBTFactory: sender is ZERO_ADDRESS");
    require(address(_sbtAddress) != address(0), "SBTFactory: SBT address is ZERO_ADDRESS");
    require(address(_beneficiary) != address(0), "SBTFactory: beneficiary is ZERO_ADDRESS");
    SBT(address(_sbtAddress)).issue(_beneficiary, _uri);
  }

  function sbtBurnerWithAddress(address _sbtAddress, uint256 _tokenId) public {
    require(address(msg.sender) != address(0), "SBTFactory: sender is ZERO_ADDRESS");
    require(address(_sbtAddress) != address(0), "SBTFactory: SBT address is ZERO_ADDRESS");
    return SBT(address(_sbtAddress)).burn(_tokenId);
  }

  function getSBTsCount(address _owner) public view returns (uint) {
    require(address(msg.sender) != address(0), "SBTFactory: sender is ZERO_ADDRESS");
    require(address(_owner) != address(0), "SBTFactory: owner is ZERO_ADDRESS");
    return tokensByOwner[_owner].length;
  }

  function getOwnerSBTs(address _owner) public view returns (address[] memory) {
    require(address(msg.sender) != address(0), "SBTFactory: sender is ZERO_ADDRESS");
    require(address(_owner) != address(0), "SBTFactory: owner is ZERO_ADDRESS");
    return tokensByOwner[_owner];
  }
}