import asyncio
from websockets.server import serve

async def echo(websocket):
    async for message in websocket:
        await websocket.send(message)

async def main():
    async with serve(echo, "localhost", 18765):
        await asyncio.get_running_loop().create_future()  # run forever

if __name__ == '__main__':
    asyncio.run(main())