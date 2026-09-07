# Implementations / DataStructures

Internal modules of the [Implementations layer](../README.md).
See [the full architecture](../../README.md) before following lower-level imports.

| Module | Responsibility |
| --- | --- |
| [BufferImplementation](BufferImplementation.lean) | Two bounded-buffer implementations with different private payment strategies |
| [GraphCursorImplementation](GraphCursorImplementation.lean) | Owned immutable adjacency lists |
| [QueueRing](QueueRing.lean) | Circular-buffer FIFO representation |
| [QueueStacksImplementation](QueueStacksImplementation.lean) | Link the two-stack FIFO to actual RAM |
| [StackImplementation](StackImplementation.lean) | Array-backed stack removal |
