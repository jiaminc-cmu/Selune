#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Tag {
    Nil = 0,
    Int = 1,
    Float = 2,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub union Payload {
    pub i: i64,
    pub f: f64,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct TValue {
    pub tag: Tag,
    _pad: [u8; 7],
    pub payload: Payload,
}

impl TValue {
    pub fn int(i: i64) -> Self {
        TValue {
            tag: Tag::Int,
            _pad: [0; 7],
            payload: Payload { i },
        }
    }
    pub fn float(f: f64) -> Self {
        TValue {
            tag: Tag::Float,
            _pad: [0; 7],
            payload: Payload { f },
        }
    }
    pub fn nil() -> Self {
        TValue {
            tag: Tag::Nil,
            _pad: [0; 7],
            payload: Payload { i: 0 },
        }
    }
}
