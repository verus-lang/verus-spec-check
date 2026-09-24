### Running tests

Enter the Nix devshell with `nix develop` to get the proper Verus version, then run tests with
`cargo test -p verus_spec_check_test`. Individual tests are runnable as such:

```bash
$ cargo test -p verus_spec_check_test --test weak_specs
```
