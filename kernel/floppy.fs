\ floppy.fs --

\ Copyright 2012 (C) Eulex Contributors

\ This file is part of Eulex.

\ Eulex is free software: you can redistribute it and/or modify
\ it under the terms of the GNU General Public License as published by
\ the Free Software Foundation, either version 3 of the License, or
\ (at your option) any later version.

\ Eulex is distributed in the hope that it will be useful,
\ but WITHOUT ANY WARRANTY; without even the implied warranty of
\ MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
\ GNU General Public License for more details.

\ You should have received a copy of the GNU General Public License
\ along with Eulex.  If not, see <http://www.gnu.org/licenses/>.

\ TODO: It is missing error checking and retries, so it will not work
\ on real hardware however I have not a real machine with floppy drive
\ to test it properly.

require @structures.fs
require @kernel/timer.fs

\ Registers
: MSR  $3F4 inputb ;
: DOR  $3F2 inputb ;    : DOR!  $3F2 outputb ;
: FIFO $3F5 inputb ;    : FIFO! $3F5 outputb ; 
: CCR! $3F7 outputb ;
: DSR! $3F4 outputb ;

\ ready to read/write?
: RQM MSR $80 and ;                             

\ Motors
variable turn?
: turn-on
    turn? @ not if DOR $10 or DOR! 300 ms turn? on then
    TIMER0 reset-timer ;

: turn-off
    turn? @ if DOR [ $10 invert ]L and DOR! turn? off then ;

\ Commands
512 constant BPS                        \ bytes per sector
18  constant SPT                        \ sectors per track
BPS SPT * 2 * constant BPC              \ bytes per cylinder

\ Throw codes for floppy drives
5 constant drive-timeout                \ Timeout
6 constant drive-unknown-err            \ Unknown error
8 constant drive-over-err               \ Too many read errors occurred, bad hardware or bad disk?

true  constant device>memory
false constant memory>device

variable irq6-received

true constant floppy-debug?

: _wait-irq ( -- ) \ throws error 5 on timeout, defaulting to stopping the word unless a catch is implimented
    time 4000 + begin dup time <= if drop 5 throw then irq6-received @ not while halt repeat drop ;

: reset-floppy
    $80 DSR! _wait-irq ; \ if this IRQ times out, there's probably a hardware problem

: wait-irq ( -- ) \ wrapper for old wait-irq that resets the controller on timeout
    ['] _wait-irq catch
    case
      5 of floppy-debug? if ." Floppy Controller Timeout! Resetting... " then reset-floppy endof
      dup throw \ pass any weird shit on
    endcase ;

: wait-ready
    128 0 ?do RQM if unloop exit endif 10 ms loop ;

: read-data  wait-ready FIFO ;
: write-data wait-ready FIFO! ;

: _command irq6-received off write-data ; 

: check-result ( n -- )
    $d0 MSR and dup $80 = if
      true return
    then drive-unknown-err throw ;

: check-irq ( n -- )
    case
      8 of false nip return endof \ sense-interrupt,
      $03 of false nip return endof \ specify
      
      true nip return \ pretty much everything else sends IRQ6
    endcase ;

: cmd-irq ( n -- ) ( wait for 10ms if command doesn't generate irq6 )
    check-irq if ['] wait-irq catch
    0 = not if reset-floppy false then else 10 ms true then ;

: command ( n -- )
    3 0 do dup _command cmd-irq if ['] check-result catch if return then then loop 8 throw ;

' write-data alias >>
' read-data  alias <<

: specify ( -- )
    $03 command $df >> $02 >> ;

: version ( -- x )
    $10 command << ;

: sense-interrupt ( -- st0 cyl )
    $08 command << << ;

: seek ( cylinder -- )
    $0f command 0 >> >> wait-irq  ;

: recalibrate
    $07 command $00 >> wait-irq ;

: xfer-ask ( s h c direction -- )
    device>memory = if $c6 else $c5 then command
    over 2 lshift  >>
    ( c ) >> ( h ) >> ( s ) >>
    2 >> 18 >> $1b >> $ff >> ;

: xfer-vry ( -- st0 st1 st2 c h s )
    << << << << << << << ( 2 ) drop ;

: read ( c h s --- st0 st1 c h s )
    swap rot device>memory xfer-ask wait-irq xfer-vry ;

: write ( c h s --- st0 st1 c h s )
    swap rot memory>device xfer-ask wait-irq xfer-vry ;

\ ISA-DMA

BPC constant dma-buffer-size

\ Align the dictionary to get a good buffer to do ISA DMA. The
\ conditions are: below 64MB and not to cross a 64KB boundary.
align
dp dma-buffer-size + dp $ffff or > [if]
    dp $ffff + $ffff0000 and dp!
[endif]
$01000000 here u<= [if]
    attr light red ." FATAL: ISA DMA Buffer is not below 64MB." cr attr!
    halt
[endif]

here dma-buffer-size allot constant dma-buffer
' dma-buffer alias floppy-buffer

: flip-flop
    $ff $0c outputb ;

: mask-dma-2 ( -- )
    $06 $0a outputb ;

: unmask-dma-2 ( -- )
    $02 $0a outputb ;

: dma-setup ( size -- ) \ this should ONLY be called from within a DMA mask of channel 2
    flip-flop
    dma-buffer ( 0 rshift ) $04 outputb \ low buffer byte 
    dma-buffer   8 rshift   $04 outputb \ high buffer byte
    dma-buffer  16 rshift   $81 outputb \ DMA page address register 2
    flip-flop 
    1- dup   $05 outputb \ set length-1 low byte
    8 rshift $05 outputb ; \ high byte

\ Setup DMA-BUFFER to a operation of reading of U bytes. Note that a
\ value of zero means $FFFF bytes.
: dma-read ( u -- )
    disable-interrupts
    mask-dma-2    
    dma-setup
    $46 $0b outputb \ mode register: Single, mem->drive, channel 2 
    unmask-dma-2
    enable-interrupts ;

\ Setup DMA-BUFFER to a operation of writing of U bytes. Note that a
\ value of zero means $FFFF bytes.
: dma-write ( u -- )
    disable-interrupts
    mask-dma-2
    dma-setup
    $4a $0b outputb \ mode register, Single, drive->mem, channel 2
    unmask-dma-2
    enable-interrupts ;

: dma>addr ( addr u -- ) \ move DMA buffer contents to address
    dma-buffer -rot move ;

: addr>dma ( addr u -- ) \ pull address contents into DMA buffer
    dma-buffer swap move ;

: read-sectors ( c h s u -- ) \ u is sector count
    turn-on
    BPS * dma-read
    -rot dup seek rot
    sense-interrupt 2drop
    read 2drop 2drop 2drop ;

: write-sectors ( c h s u -- ) \ u is sector count
    turn-on
    BPS * dma-write
    -rot dup seek rot
    sense-interrupt 2drop
    write 2drop 2drop 2drop ;

: read-cylinder ( c -- )
    0 1 SPT 2* read-sectors ;

: write-cylinder ( c -- )
    0 1 SPT 2* write-sectors ;

: detect-drive ( -- flag ) \ TODO: support slave drive
    $10 $70 outputb \ select floppy register
    $71 inputb 4 rshift 4 = ; \ pull register contents, bits 4-7 are drive 0

: setup-floppy
    $00 CCR! ;

: irq-floppy
    irq6-received on
; 6 IRQ

: drive-init
    detect-drive not if exit then
    2000 ['] turn-off TIMER0 set-timer
    irq6-received off
    reset-floppy
    sense-interrupt 2drop
    setup-floppy
    specify
    turn-on
    recalibrate
    sense-interrupt 2drop
    turn-off ;

: initialize-floppy ['] drive-init catch 0 = if true else false then ;

: floppy-read-sectors ( addr u c h s -- )
    3 pick read-sectors 512 * dma>addr ;

: floppy-write-sectors ( addr u c h s -- )
    3 pick >r >r >r >r 512 * addr>dma
    r> r> r> r> write-sectors ;

: lba ( lba -- c h s )
    dup SPT 2* /
    over SPT 2* mod SPT /
    rot SPT mod 1+ ;

\ floppy.fs ends here
