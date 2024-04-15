use bytemuck::{Pod, Zeroable};

pub trait IntoEntian<T> {
    fn into_le(self) -> T;
    fn into_be(self) -> T;
}

macro_rules! impl_ints {
    ($type:ident, $int:ident) => {
        impl IntoEntian<$type> for $int {
            fn into_le(self) -> $type {
                $type::from_le(self)
            }

            fn into_be(self) -> $type {
                $type::from_be(self)
            }
        }

        impl $type {
            pub fn get_le(&self) -> $int {
                $int::from_le_bytes(self.0)
            }

            pub fn get_be(&self) -> $int {
                $int::from_be_bytes(self.0)
            }

            pub fn from_le(val: $int) -> Self {
                Self($int::to_le_bytes(val))
            }

            pub fn from_be(val: $int) -> Self {
                Self($int::to_be_bytes(val))
            }
        }
    };
}

impl std::convert::From<bool> for U8 {
    fn from(value: bool) -> Self {
        Self(if value { 1 } else { 0u8 }.to_le_bytes())
    }
}

#[repr(C)]
#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct U8([u8; 1]);
#[repr(C)]
#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct U16([u8; 2]);
#[repr(C)]
#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct U32([u8; 4]);
#[repr(C)]
#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct USize([u8; 8]);

impl_ints!(U8, u8);
impl_ints!(U16, u16);
impl_ints!(U32, u32);
impl_ints!(USize, u64);

#[repr(C, packed)]
#[derive(Clone, Copy)]
struct Header {
    magic: [u8; 4],
    class: U8,
    data: U8,
    version: U8,
    osabi: U8,
    abiversion: U8,
    pad: [u8; 7],
    f_type: U16,
    machine: U16,
    version_2: U32,
    entry: USize,
    program_header_off: USize,
    section_header_off: USize,
    flags: U32,
    header_size: U16,

    program_header_size: U16,
    program_header_num: U16,

    section_header_size: U16,
    section_header_num: U16,

    index_section_header_names: U16,
}

unsafe impl Pod for Header {}
unsafe impl Zeroable for Header {}

#[repr(C, packed)]
#[derive(Default, Clone, Copy)]
struct ProgramHeader {
    p_type: U32,
    flags: U32,
    file_offset: USize,
    virtual_addr: USize,
    physical_addr: USize,
    file_size: USize,
    mem_size: USize,
    align: USize,
}
unsafe impl Pod for ProgramHeader {}
unsafe impl Zeroable for ProgramHeader {}

#[repr(C, packed)]
#[derive(Default, Clone, Copy)]
struct SectionHeader {
    name_off: U32,
    s_type: U32,
    flags: USize,
    virtual_address: USize,
    file_off: USize,
    file_size: USize,
    link: U32,
    info: U32,
    addr_align: USize,
    ent_size: USize,
}

unsafe impl Pod for SectionHeader {}
unsafe impl Zeroable for SectionHeader {}

#[repr(C, packed)]
#[derive(Default, Clone, Copy)]
struct SymbolTableEntry {
    name: U32,
    info: U8,
    other: U8,
    section_index: U16,
    addr: USize,
    sym_size: USize,
}

unsafe impl Pod for SymbolTableEntry {}
unsafe impl Zeroable for SymbolTableEntry {}

pub fn write_elf(file: &mut impl std::io::Write, instructions: &[u8]) -> std::io::Result<()> {
    const PROGRAM_HEADERS: usize = 1;
    const SECTION_HEADERS: usize = 4;
    const SYMBOLS: usize = 2;
    const PROGRAM_ALIGN: u64 = 0x1000;
    const PROGRAM_START: u64 = 0x401000;

    macro_rules! construct_str_table {
        ($vis:vis mod $mode_name:ident{$table_name:ident, $($name:ident:$str:expr $(,)?)*}) => {
            $vis mod $mode_name{
                construct_str_table!("", $($name:$str),*);
                pub const $table_name: &str = concat!($(concat!($str, '\0'),)*);
            }
        };
        ($existing:expr, $name:ident:$str:expr, $($name_repr:ident:$str_repr:expr),*) => {
            pub const $name: usize = $existing.len();
            construct_str_table!(concat!($existing, $str, '\0'), $($name_repr:$str_repr),*);
        };
        ($existing:expr, $name:ident:$str:expr) => {
            pub const $name: usize = $existing.len();
        };
        ($existing:expr) => {
        };
    }

    construct_str_table!(mod str_table{TABLE, _EMPTY:"",TEXT:".text", STRTAB:".strtab", SYMTAB:".symtab", START:"_start"});

    let elf_header_start = 0;
    let program_header_start = elf_header_start + std::mem::size_of::<Header>();
    let section_header_start =
        program_header_start + std::mem::size_of::<ProgramHeader>() * PROGRAM_HEADERS;
    let str_table_start =
        section_header_start + std::mem::size_of::<SectionHeader>() * SECTION_HEADERS;

    let symbol_table_start = str_table_start + str_table::TABLE.len();

    let program_start_unaligned =
        symbol_table_start + std::mem::size_of::<SymbolTableEntry>() * SYMBOLS;

    let program_start_file =
        ((program_start_unaligned as u64 + PROGRAM_ALIGN - 1) / PROGRAM_ALIGN) * PROGRAM_ALIGN;

    let programs: [ProgramHeader; PROGRAM_HEADERS] = [ProgramHeader {
        p_type: 1.into_le(),  // PT_LOAD
        flags: 0x5.into_le(), // PT_READ PT_EXECUTE
        file_offset: program_start_file.into_le(),
        virtual_addr: PROGRAM_START.into_le(),
        physical_addr: PROGRAM_START.into_le(),
        file_size: (instructions.len() as u64).into_le(),
        mem_size: (instructions.len() as u64).into_le(),
        align: PROGRAM_ALIGN.into_le(),
    }];

    let sections: [SectionHeader; SECTION_HEADERS] = [
        SectionHeader::default(),
        SectionHeader {
            name_off: (str_table::STRTAB as u32).into_le(),
            s_type: 0x3.into_le(), // zero terminated string
            flags: 0.into_le(),
            virtual_address: 0.into_le(),
            file_off: (str_table_start as u64).into_le(),
            file_size: (str_table::TABLE.len() as u64).into_le(),
            link: 0.into_le(),
            info: 0.into_le(),
            addr_align: 1.into_le(),
            ent_size: 0.into_le(),
        },
        SectionHeader {
            name_off: (str_table::SYMTAB as u32).into_le(),
            s_type: 0x2.into_le(), // symbol table
            flags: 0.into_le(),
            virtual_address: 0.into_le(),
            file_off: (symbol_table_start as u64).into_le(),
            file_size: ((std::mem::size_of::<SymbolTableEntry>() * SYMBOLS) as u64).into_le(),
            link: 1.into_le(), // str table
            info: 1.into_le(), // first global symbol
            addr_align: 1.into_le(),
            ent_size: (std::mem::size_of::<SymbolTableEntry>() as u64).into_le(),
        },
        SectionHeader {
            name_off: (str_table::TEXT as u32).into_le(),
            s_type: 1.into_le(), // SHT_PROGBITS
            flags: 6.into_le(),  // flags A(allocate in image?) X(exacutable?)
            virtual_address: PROGRAM_START.into_le(),
            file_off: (program_start_file as u64).into_le(),
            file_size: (instructions.len() as u64).into_le(),
            link: 0.into_le(),
            info: 0.into_le(),
            addr_align: PROGRAM_ALIGN.into_le(),
            ent_size: 0.into_le(),
        },
    ];

    let symbols: [SymbolTableEntry; SYMBOLS] = [
        SymbolTableEntry::default(),
        SymbolTableEntry {
            name: (str_table::START as u32).into_le(),
            info: (0x12).into_le(),     //global function
            other: 0.into_le(),         // default
            section_index: 3.into_le(), //program section
            addr: PROGRAM_START.into_le(),
            sym_size: (instructions.len() as u64).into_le(),
        },
    ];

    let header = Header {
        magic: [0x7f, 0x45, 0x4c, 0x46],
        class: 2.into_le(),   // 64 bit
        data: 1.into_le(),    // le
        version: 1.into_le(), //version 1
        osabi: 9.into_le(),   // system-v(0) freebsd(9)
        abiversion: 0.into_le(),
        pad: [0; 7],
        f_type: 2.into_le(),     // executable file
        machine: 0x3E.into_le(), // x86-64
        version_2: 1.into_le(),
        entry: PROGRAM_START.into_le(),
        program_header_off: (program_header_start as u64).into_le(),
        section_header_off: (section_header_start as u64).into_le(),
        flags: 0.into_le(),
        header_size: (std::mem::size_of::<Header>() as u16).into_le(),
        program_header_size: (std::mem::size_of::<ProgramHeader>() as u16).into_le(),
        program_header_num: (PROGRAM_HEADERS as u16).into_le(),
        section_header_size: (std::mem::size_of::<SectionHeader>() as u16).into_le(),
        section_header_num: (SECTION_HEADERS as u16).into_le(),
        index_section_header_names: 1.into_le(),
    };
    file.write_all(bytemuck::bytes_of(&header))?;

    for ph in &programs {
        file.write_all(bytemuck::bytes_of(ph))?;
    }

    for section in &sections {
        file.write_all(bytemuck::bytes_of(section))?;
    }

    file.write_all(str_table::TABLE.as_bytes())?;

    for symbol in &symbols {
        file.write_all(bytemuck::bytes_of(symbol))?;
    }

    // alignment
    for _ in program_start_unaligned..(program_start_file as usize) {
        file.write_all(&[0])?;
    }

    file.write_all(instructions)
}
