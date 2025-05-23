pub mod seq_helper;

// Logical atomicity experiments, mechanizing write-restricted storage.
pub mod pairdisk;
pub mod frac_ptsto;

// Per-address separation logic for a disk.
pub mod map_view;
pub mod seq_view;
pub mod vecdisk;
pub mod disk_wrap;
pub mod disk_wrap_lib;
pub mod allocator;

// Misc code.
pub mod ziqiao_frac_perm;
pub mod typeinv;

pub mod seq_prefix;
