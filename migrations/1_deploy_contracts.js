const SBTFactory = artifacts.require("SBTFactory");

module.exports = function(deployer) {
  deployer.deploy(SBTFactory);
};