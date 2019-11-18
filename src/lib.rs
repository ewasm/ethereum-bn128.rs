// Copyright 2015-2018 Parity Technologies (UK) Ltd.
// This file is part of Parity.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

extern crate bn;
extern crate rustc_hex;

use std::io::{self, Read};

#[derive(Debug)]
pub struct Error(pub &'static str);

impl From<&'static str> for Error {
    fn from(val: &'static str) -> Self {
        Error(val)
    }
}

fn read_fr(reader: &mut io::Chain<&[u8], io::Repeat>) -> Result<::bn::Fr, Error> {
    let mut buf = [0u8; 32];

    reader
        .read_exact(&mut buf[..])
        .expect("reading from zero-extended memory cannot fail; qed");
    ::bn::Fr::from_slice(&buf[0..32]).map_err(|_| Error::from("Invalid field element"))
}

fn read_point(reader: &mut io::Chain<&[u8], io::Repeat>) -> Result<::bn::G1, Error> {
    use bn::{AffineG1, Fq, Group, G1};

    let mut buf = [0u8; 32];

    reader
        .read_exact(&mut buf[..])
        .expect("reading from zero-extended memory cannot fail; qed");
    let px = Fq::from_slice(&buf[0..32]).map_err(|_| Error::from("Invalid point x coordinate"))?;

    reader
        .read_exact(&mut buf[..])
        .expect("reading from zero-extended memory cannot fail; qed");
    let py = Fq::from_slice(&buf[0..32]).map_err(|_| Error::from("Invalid point y coordinate"))?;
    Ok(if px == Fq::zero() && py == Fq::zero() {
        G1::zero()
    } else {
        AffineG1::new(px, py)
            .map_err(|_| Error::from("Invalid curve point"))?
            .into()
    })
}

// Can fail if any of the 2 points does not belong the bn128 curve
pub fn bn128_add(input: &[u8], output: &mut [u8; 64]) -> Result<(), Error> {
    use bn::AffineG1;

    let mut padded_input = input.chain(io::repeat(0));
    let p1 = read_point(&mut padded_input)?;
    let p2 = read_point(&mut padded_input)?;

    let mut write_buf = [0u8; 64];
    if let Some(sum) = AffineG1::from_jacobian(p1 + p2) {
        // point not at infinity
        sum.x()
            .to_big_endian(&mut write_buf[0..32])
            .expect("Cannot fail since 0..32 is 32-byte length");
        sum.y()
            .to_big_endian(&mut write_buf[32..64])
            .expect("Cannot fail since 32..64 is 32-byte length");
    }
    *output = write_buf;

    Ok(())
}

// Can fail if first paramter (bn128 curve point) does not actually belong to the curve
pub fn bn128_mul(input: &[u8], output: &mut [u8; 64]) -> Result<(), Error> {
    use bn::AffineG1;

    let mut padded_input = input.chain(io::repeat(0));
    let p = read_point(&mut padded_input)?;
    let fr = read_fr(&mut padded_input)?;

    let mut write_buf = [0u8; 64];
    if let Some(sum) = AffineG1::from_jacobian(p * fr) {
        // point not at infinity
        sum.x()
            .to_big_endian(&mut write_buf[0..32])
            .expect("Cannot fail since 0..32 is 32-byte length");
        sum.y()
            .to_big_endian(&mut write_buf[32..64])
            .expect("Cannot fail since 32..64 is 32-byte length");
    }
    *output = write_buf;

    Ok(())
}

/// Can fail if:
///     - input length is not a multiple of 192
///     - any of odd points does not belong to bn128 curve
///     - any of even points does not belong to the twisted bn128 curve over the field F_p^2 = F_p[i] / (i^2 + 1)
pub fn bn128_pairing(input: &[u8], output: &mut [u8; 32]) -> Result<(), Error> {
    use bn::{pairing_batch, AffineG1, AffineG2, Fq, Fq2, Group, Gt, G1, G2};

    if input.len() % 192 != 0 {
        return Err("Invalid input length, must be multiple of 192 (3 * (32*2))".into());
    }

    let elements = input.len() / 192; // (a, b_a, b_b - each 64-byte affine coordinates)
    let ret_val = if input.len() == 0 {
        bn::arith::U256::one()
    } else {
        let mut vals = Vec::new();
        for idx in 0..elements {
            let a_x = Fq::from_slice(&input[idx * 192..idx * 192 + 32])
                .map_err(|_| Error::from("Invalid a argument x coordinate"))?;

            let a_y = Fq::from_slice(&input[idx * 192 + 32..idx * 192 + 64])
                .map_err(|_| Error::from("Invalid a argument y coordinate"))?;

            let b_a_y = Fq::from_slice(&input[idx * 192 + 64..idx * 192 + 96])
                .map_err(|_| Error::from("Invalid b argument imaginary coeff x coordinate"))?;

            let b_a_x = Fq::from_slice(&input[idx * 192 + 96..idx * 192 + 128])
                .map_err(|_| Error::from("Invalid b argument imaginary coeff y coordinate"))?;

            let b_b_y = Fq::from_slice(&input[idx * 192 + 128..idx * 192 + 160])
                .map_err(|_| Error::from("Invalid b argument real coeff x coordinate"))?;

            let b_b_x = Fq::from_slice(&input[idx * 192 + 160..idx * 192 + 192])
                .map_err(|_| Error::from("Invalid b argument real coeff y coordinate"))?;

            let b_a = Fq2::new(b_a_x, b_a_y);
            let b_b = Fq2::new(b_b_x, b_b_y);
            let b = if b_a.is_zero() && b_b.is_zero() {
                G2::zero()
            } else {
                G2::from(
                    AffineG2::new(b_a, b_b)
                        .map_err(|_| Error::from("Invalid b argument - not on curve"))?,
                )
            };
            let a = if a_x.is_zero() && a_y.is_zero() {
                G1::zero()
            } else {
                G1::from(
                    AffineG1::new(a_x, a_y)
                        .map_err(|_| Error::from("Invalid a argument - not on curve"))?,
                )
            };
            vals.push((a, b));
        }

        let mul = pairing_batch(&vals);

        if mul == Gt::one() {
            bn::arith::U256::one()
        } else {
            bn::arith::U256::zero()
        }
    };

    ret_val
        .to_big_endian(output)
        .expect("Cannot fail since 0..32 is 32-byte length");

    Ok(())
}

#[cfg(test)]
mod tests {
    use rustc_hex::FromHex;

    use super::{bn128_add, bn128_mul, bn128_pairing};

    #[test]
    fn test_bn128_add() {
        // zero-points additions
        {
            let input = FromHex::from_hex(
                "\
                 0000000000000000000000000000000000000000000000000000000000000000\
                 0000000000000000000000000000000000000000000000000000000000000000\
                 0000000000000000000000000000000000000000000000000000000000000000\
                 0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap();

            let mut output = [0u8; 64];
            let expected = FromHex::from_hex(
                "\
                 0000000000000000000000000000000000000000000000000000000000000000\
                 0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap();

            bn128_add(&input[..], &mut output).expect("Builtin should not fail");
            assert_eq!(output.to_vec(), expected);
        }

        // no input, should not fail
        {
            let empty_input = [0u8; 0];

            let mut output = [0u8; 64];
            let expected = FromHex::from_hex(
                "\
                 0000000000000000000000000000000000000000000000000000000000000000\
                 0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap();

            bn128_add(&empty_input[..], &mut output).expect("Builtin should not fail");
            assert_eq!(output.to_vec(), expected);
        }

        // should fail - point not on curve
        {
            let input = FromHex::from_hex(
                "\
                 1111111111111111111111111111111111111111111111111111111111111111\
                 1111111111111111111111111111111111111111111111111111111111111111\
                 1111111111111111111111111111111111111111111111111111111111111111\
                 1111111111111111111111111111111111111111111111111111111111111111",
            )
            .unwrap();

            let mut output = [0u8; 64];

            let res = bn128_add(&input[..], &mut output);
            assert!(res.is_err(), "There should be built-in error here");
        }

        // should pass.  Points all on curve
        {
            let valid_inputs = [
            "2a0ac60fb814fba447543a4da1822b2ce278326c58584f2f9ac622c76d4c3bc51a4e5b20c4d93d726932c8eb869a2f3a0ee15bd0e8e33800b81716e3184a8bd717a0ccf9aff623d77a12371703e6723fdd1fc7bca44df12afcf9a1ff9ed93c652448d8a2f6e31920a16efdc40d318cd939e0c4e29253acd555d01c1cc070106f",
            "208e3b39b54d99dda4b719e49d3c6ab46e944f53a3b6d7e61751d6c01411b9e51fc7acbd97b4e6e7ab7afa120e2d851536e1a35b3f4e4b307e909917906429c1069685ee8568fbae948b6684f73c272220fab47d1a10981c1835bdc8a749b3a114b1f347c5a2c1429f1aaf4acf8841d26b2d74679b7a1cc01ebcfadd1d2092a5",
            "2e44c058a4913221a14da40bd95c7149da3a92adadebc4ee2552bb5ae770449e06f845022ecf2d014803e5d3038d5f2e079dce17833f9ce5627657a3da5223f22e80c5ee39d3b17e48b7f5375ede609a7a3b77530283d9f3c044c9ba923846bc03ae306319c44b6e9af81661506c28014c438dd55237d18451f2ea8f216b62ed",
            "2762b457c413e77e752f024eb6e7bccbf51a1bb7cc1c9ee5ae35b348d4d32a621ef2b7419b8d5de02719d36f3a4a9f14655819634e9ba73fc62c2b5bc6f4cc9e0fd1a4daabcb8fe11d27e2080130a1c118d426ecaaf6eb221471e67d2b396c1a1b215949ad86e252a3fadaa8cd765c314a78bd1eef7dd73d7d27693e89632f20",
            "1e3eb253f57eb46959dc7e7f95f66de0b835143a497a793d1f5cd8ad54cc87002fe6d1658419f152572edc2a7587718d755b646a2ad7ba425d79dc1ba9f15c2a080de808e71d9ef729bb754d291cce7928c535d5715141400d94f259bba8e06c2f0b91e1641a153ebeb764b258e70c01dff9e8af769fb1d120b7f0cfe7b0b7d2",
            "0191a03fcf6278e44a70bdb41f2f7c09040401f1fd445d5c0e334518a6b6586728fadfeb3188556e5d23c1153f2af903c0591e915645f2c820c66ddb7468376d266a859b3546981899bff55841c9868e641121400db401bf834666b5cff59b581e9702e58efcc4c9b3af1edf5ce88929a8b0c9a475a0208a08356229324de106",
            "2cc994b0d95f47a2302350cf87a6d7f3067ecce4256b4e4ee9ff555f8bc752be296d2db2bbe0aac9e1ad5d2ad14b44b2c7954d246b3d53c8227d47a23505120d09c7b72efea24f9c871bc9a129a9ee68fd17786398faae8e6e66c9f1784ffa1318b7bc0f9e4f0bbb9c4b6e6ccda715aa4cf35986da25aa54ef4e645a45f9b9d0",
            "05f0aef930d65535c69ac6a9f3621128d8ac6cccddfa21f67e3bba9a87f0cca314cdf7f81f5fa8e91408115c81428722bfd94112913f2710d41d89f765f815d5229634e3272a62687faeb95485411046bf3925c0e4f070bc8e078be62c9568a02d13ace3b3c2b76adae6c7d0b1df6b5df22548194d42c06de695e2c0cedbb14f",
            "05e66c3ad55608059530bc6ed3f59181e60f7a7de755d1e189ea2318fef87d482d457701d36f49713a2c8cb80fe8f38e539336acaeb58f00b097daea5850a0680593ed4fe3d069642197b8176b71adc97749b7d094ae1d1ce227c20b7323643d12c25f82c50f1f1f537df9ddd8191e6f0ad14d287c2ee64d357a4a0a0aecb46f",
            "0b63392bf6630439a354ca4beede4fed5ed6259ddc6c201378e8638d993ee243240e3f7407f2f7fcf5dda8d3ce9511d1f703e984deab6a72465e792d80dd07202bdccbde7c3ee6a23316ffb04c24a369e6db509a55789fd38128ec249b2f6c731a97f988863ee15674a42ecff446b59854ea6ee2f62b5615e5eda149a2e0015b",
            "1af34655c9efe4b5a938b78cfe9c9298fc7f91553dcd35854157e47ec87541de040abca37739bfaed962b25092e0be5d68144be0e07051785486489eeb74007a2d199f0e515eec242e675e0077b03990e7032297934402a3e7b95305f26fb4fd202513fdc6f701ecfb070cd3d0fa41e34b4248ab2789deed43a0f1a86e03d49d",
            "133ec1c59b570a5881f6f6c1859570904f1838bc7cbefa2530512674c024b471019ba55c289594ebc3c62acd7366f98712424e9e25e23f14dc8a96f0a372b618130d0168220cd98ffea68c396d6482ecaefcd92eec121318dfe5c9a88e920cf52d139bc10df0a6d1c044c1ecf2c1c3be612725dfae8fc44e980a469e920cfe20",
            "1ff6fb6060c147e179ccb295677065d6ff441663c71e7e0c07d494f26ba07fcb2c816f9845fa0cda9a5ed30022c89f0f137f157c6bc1f6d3fb49e849873869bb24aae0b8a7cebaa4cb7d32e7745ac43362a5a5cbce60115b0208925c37a44c272f5a28af9605a7ee906ac12b9430208d79947fb50528c4e582b3af752c8cb9b6",
            "1192eaa18f04a2b0681411d8e2e15785f28b4ed976e5ee083679d3bade80b9ab17c2e982c30b1f39d4717fa9f5be7d16a74caea175889cd47a5f0f368b017e6821739276bdee922324ff401091a8782d821b7fef8f2ed34f7fcf4423b51cf8410fc04fab89a2154b88345314450d14dac77ff35a9a808e9e8cb8aaa63f9c20b7",
            "185fe3c8f22b14cd17d9e22fd3eabdabb94ad03c6380b06a8a2eec1064cc12870e321fc5eafe6c6822ece5680f53d1c4f0f301c243e6e5360f6b8d8639b504f319ceccfb6d6a85cfd3025118739ecd5a54d361bfcec02a8b46aaf14e6f780b9622f6220ae7b977b473cc5a0817ad3a85452eda43161fe4e67f4d4ab3a8c1f187",
            "0f12c62f6389a5713ac78140f85777d096ebd99e2e05cadeb3c04551696b0c6e2cec157750cf47b6b9d51a072a98514da43facab9759382cb784c55de2f93ea91cd928c10ff4807f4cab035678aee47444908bbd7ccf32c7493029763673f69f22ba795cd879885e208614559d3c8c28c00ae0056c2cb3823e582b0e037e3a0f",
            "2f2e1551f6c6b62286efc48e65dc0773a6279c98fa0560c333d7f389c03b5843304f068f909bfc1a3cece08a8375bf324261e80b1e538754b4b4e9be7fdcaae40bc6b1688a8352f2081c12bf83e8c05aa04ce2ddab948cf36c73059a54d650e71d6a367598c88d9f7498c4242f003f91ab40fcf7a27a921b18279f723a43b6e4",
            "1f8b0a41634c43a8661112b3723a2f55a87904543003597ac04ddbaae9046d2f0858849758cceedb449b96a352bb0e7c8c25d4578b5bd89081bf9c6d0557442e0ce5a266dde51e9a91272a0f9054d9d406e42e666eabf2f9c6db65085f2a45d11d1bee349549a3e6053f33dae151aec561ec3c7a16eb4a739b81ccfc376f6e24",
            "2030eafc21d7b91698284721b472020bb07b64dba78e62ca73456f2b712ef0621250da0153c33c131dbe8ca29a4564ad94e81e6ec2961fb3b8830181cb2eb28f2ddbb22e58fb87a32abca173935666aff24a2da1ddc7d9bdf89f7864819c374e0f7e782a59e42e138f73c068b0c61b46f4fa5e7e29082d55f0bea49ecbfce85b",
            "2ae7165687e08e5f1e013ca0e57622492e7f92506667487ffc30df2c3befd04711d9387c823fb988efba8c599f0810dd37be7a33571ff21a0ec21b42603818cf1f827b775b17581d04e9262c728a560bb8916de5ebb69bb7fde17530c5a8901206b0a4361f9feebd5ffee40761d7e922fc4c776e6f7e4f24f8f73a973b6bbbdb"];

            let mut output = [0u8; 64];
            let expected = FromHex::from_hex(
                "\
                 0000000000000000000000000000000000000000000000000000000000000000\
                 0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap();

            for x in valid_inputs.iter() {
                let input = x.from_hex().expect("wasn't valid hex");

                bn128_add(&input[..], &mut output).expect("Builtin should not fail");
                assert_eq!(output.to_vec(), expected);
            }
        }
    }

    #[test]
    fn test_bn128_mul() {
        // zero-point multiplication
        {
            let input = FromHex::from_hex(
                "\
                 0000000000000000000000000000000000000000000000000000000000000000\
                 0000000000000000000000000000000000000000000000000000000000000000\
                 0200000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap();

            let mut output = [0u8; 64];
            let expected = FromHex::from_hex(
                "\
                 0000000000000000000000000000000000000000000000000000000000000000\
                 0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap();

            bn128_mul(&input[..], &mut output).expect("Builtin should not fail");
            assert_eq!(output.to_vec(), expected);
        }

        // should fail - point not on curve
        {
            let input = FromHex::from_hex(
                "\
                 1111111111111111111111111111111111111111111111111111111111111111\
                 1111111111111111111111111111111111111111111111111111111111111111\
                 0f00000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap();

            let mut output = [0u8; 64];

            let res = bn128_mul(&input[..], &mut output);
            assert!(res.is_err(), "There should be built-in error here");
        }
    }

    fn pairing_empty_test(expected: Vec<u8>) {
        let empty_input = [0u8; 0];
        let mut output = [0u8; 32];

        bn128_pairing(&empty_input[..], &mut output).expect("Builtin should not fail");
        assert_eq!(output.to_vec(), expected);
    }

    fn pairing_error_test(input: &[u8], msg_contains: Option<&str>) {
        let mut output = [0u8; 32];
        let res = bn128_pairing(input, &mut output);
        if let Some(msg) = msg_contains {
            if let Err(e) = res {
                if !e.0.contains(msg) {
                    panic!(
                        "There should be error containing '{}' here, but got: '{}'",
                        msg, e.0
                    );
                }
            }
        } else {
            assert!(res.is_err(), "There should be built-in error here");
        }
    }

    fn bytes(s: &'static str) -> Vec<u8> {
        FromHex::from_hex(s).expect("static str should contain valid hex bytes")
    }

    #[test]
    // should pass (multi-point example taken from ethereum test case 'pairingTest')
    fn bn128_pairing_multi_point() {
        let pairing_input = FromHex::from_hex("2eca0c7238bf16e83e7a1e6c5d49540685ff51380f309842a98561558019fc0203d3260361bb8451de5ff5ecd17f010ff22f5c31cdf184e9020b06fa5997db841213d2149b006137fcfb23036606f848d638d576a120ca981b5b1a5f9300b3ee2276cf730cf493cd95d64677bbb75fc42db72513a4c1e387b476d056f80aa75f21ee6226d31426322afcda621464d0611d226783262e21bb3bc86b537e986237096df1f82dff337dd5972e32a8ad43e28a78a96a823ef1cd4debe12b6552ea5f06967a1237ebfeca9aaae0d6d0bab8e28c198c5a339ef8a2407e31cdac516db922160fa257a5fd5b280642ff47b65eca77e626cb685c84fa6d3b6882a283ddd1198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa").unwrap();
        let mut output = [0u8; 32];
        let mut output_expected = [0u8; 32];
        output_expected[31] = 1u8;
        bn128_pairing(&pairing_input, &mut output).expect("pairing check failed");
        assert!(
            output_expected == output,
            "pairing check did not evaluate to 1"
        );
    }

    #[test]
    fn bn128_pairing_empty() {
        // should not fail, because empty input is a valid input of 0 elements
        pairing_empty_test(bytes(
            "0000000000000000000000000000000000000000000000000000000000000001",
        ));
    }

    #[test]
    fn bn128_pairing_notcurve() {
        // should fail - point not on curve
        pairing_error_test(
            &bytes(
                "\
                 1111111111111111111111111111111111111111111111111111111111111111\
                 1111111111111111111111111111111111111111111111111111111111111111\
                 1111111111111111111111111111111111111111111111111111111111111111\
                 1111111111111111111111111111111111111111111111111111111111111111\
                 1111111111111111111111111111111111111111111111111111111111111111\
                 1111111111111111111111111111111111111111111111111111111111111111",
            ),
            Some("not on curve"),
        );
    }

    #[test]
    fn bn128_pairing_fragmented() {
        // should fail - input length is invalid
        pairing_error_test(
            &bytes(
                "\
                 1111111111111111111111111111111111111111111111111111111111111111\
                 1111111111111111111111111111111111111111111111111111111111111111\
                 111111111111111111111111111111",
            ),
            Some("Invalid input length"),
        );
    }
}
