use std::io;
use std::io::Write;

#[allow(unused)]
macro_rules! write_stdout {
    ($($arg:tt)*) => {
        let _ = write!(crate::stdout::RawStdioWrite {}, $($arg)*);
    };
}

#[allow(unused_imports)]
pub(crate) use write_stdout;

pub(crate) struct RawStdioWrite {}

impl Write for RawStdioWrite {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        unsafe { stdout_write(buf as *const _ as _, buf.len()) };
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        unsafe { stdout_flush() };
        Ok(())
    }
}

extern "C" {
    fn stdout_write(buf: *const (), count: usize);
    fn stdout_flush();
}
