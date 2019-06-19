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
extern crate parity_bytes as bytes;
extern crate rustc_hex;

use std::io::{self, Read};

use bytes::BytesRef;

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
pub fn bn128_add(input: &[u8], output: &mut BytesRef) -> Result<(), Error> {
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
    output.write(0, &write_buf);

    Ok(())
}

// Can fail if first paramter (bn128 curve point) does not actually belong to the curve
pub fn bn128_mul(input: &[u8], output: &mut BytesRef) -> Result<(), Error> {
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
    output.write(0, &write_buf);
    Ok(())
}

/// Can fail if:
///     - input length is not a multiple of 192
///     - any of odd points does not belong to bn128 curve
///     - any of even points does not belong to the twisted bn128 curve over the field F_p^2 = F_p[i] / (i^2 + 1)
pub fn bn128_pairing(input: &[u8], output: &mut BytesRef) -> Result<(), Error> {
    use bn::{pairing, AffineG1, AffineG2, Fq, Fq2, Group, Gt, G1, G2};

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

        let mul = vals
            .into_iter()
            .fold(Gt::one(), |s, (a, b)| s * pairing(a, b));

        if mul == Gt::one() {
            bn::arith::U256::one()
        } else {
            bn::arith::U256::zero()
        }
    };

    let mut buf = [0u8; 32];
    ret_val
        .to_big_endian(&mut buf)
        .expect("Cannot fail since 0..32 is 32-byte length");;
    output.write(0, &buf);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{bn128_add, bn128_mul, bn128_pairing};
    use bytes::BytesRef;
    use rustc_hex::FromHex;

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

            let mut output = vec![0u8; 64];
            let expected = FromHex::from_hex(
                "\
                 0000000000000000000000000000000000000000000000000000000000000000\
                 0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap();

            bn128_add(&input[..], &mut BytesRef::Fixed(&mut output[..]))
                .expect("Builtin should not fail");
            assert_eq!(output, expected);
        }

        // no input, should not fail
        {
            let mut empty = [0u8; 0];
            let input = BytesRef::Fixed(&mut empty);

            let mut output = vec![0u8; 64];
            let expected = FromHex::from_hex(
                "\
                 0000000000000000000000000000000000000000000000000000000000000000\
                 0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap();

            bn128_add(&input[..], &mut BytesRef::Fixed(&mut output[..]))
                .expect("Builtin should not fail");
            assert_eq!(output, expected);
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

            let mut output = vec![0u8; 64];

            let res = bn128_add(&input[..], &mut BytesRef::Fixed(&mut output[..]));
            assert!(res.is_err(), "There should be built-in error here");
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

            let mut output = vec![0u8; 64];
            let expected = FromHex::from_hex(
                "\
                 0000000000000000000000000000000000000000000000000000000000000000\
                 0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap();

            bn128_mul(&input[..], &mut BytesRef::Fixed(&mut output[..]))
                .expect("Builtin should not fail");
            assert_eq!(output, expected);
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

            let mut output = vec![0u8; 64];

            let res = bn128_mul(&input[..], &mut BytesRef::Fixed(&mut output[..]));
            assert!(res.is_err(), "There should be built-in error here");
        }
    }

    fn pairing_empty_test(expected: Vec<u8>) {
        let mut empty = [0u8; 0];
        let input = BytesRef::Fixed(&mut empty);

        let mut output = vec![0u8; expected.len()];

        bn128_pairing(&input[..], &mut BytesRef::Fixed(&mut output[..]))
            .expect("Builtin should not fail");
        assert_eq!(output, expected);
    }

    fn pairing_error_test(input: &[u8], msg_contains: Option<&str>) {
        let mut output = vec![0u8; 64];
        let res = bn128_pairing(input, &mut BytesRef::Fixed(&mut output[..]));
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
